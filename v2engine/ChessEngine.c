#include <stdint.h>
#include <stdbool.h>
#include "ChessState.h"

/* === CBMC integration (no headers required) === */
extern uint16_t nondet_uint16_t(void);
void __CPROVER_assume(_Bool);

/* ===== Move encoding utilities (12 bits total) =====
   Layout: bits 0..2=srcRow, 3..5=srcCol, 6..8=dstRow, 9..11=dstCol
   Value range: 0..4095  (8*8*8*8)
*/
static inline uint16_t encode12(int sr, int sc, int dr, int dc) {
  return (uint16_t)((sr & 7) | ((sc & 7) << 3) | ((dr & 7) << 6) | ((dc & 7) << 9));
}
static inline void decode12(uint16_t code, int *sr, int *sc, int *dr, int *dc) {
  *sr = (int)(code & 7u);
  *sc = (int)((code >> 3) & 7u);
  *dr = (int)((code >> 6) & 7u);
  *dc = (int)((code >> 9) & 7u);
}

/* Value by *piece code* (0, 1..6, 9..14) -> centipawns. */
static inline int value_of_piece_code(uint8_t pc) {
  return PIECE_VALUE_BY_TYPE[piece_type(pc)];
}

static inline int same_color(uint8_t a, uint8_t b) {
  if (a == EMPTY || b == EMPTY) return 0;
  return (is_white_piece(a) && is_white_piece(b)) || (is_black_piece(a) && is_black_piece(b));
}

/* === Attack detection (used for king safety) ===
   Minimal loops: rays are length-bounded by 7.
*/
static bool square_attacked_by(const ChessState *s, int r, int c, bool by_white) {
  /* Pawns */
  if (by_white) {
    int pr = r + 1;
    if (in_bounds(pr, c - 1) && s->board[pr][c - 1] == W_PAWN) return true;
    if (in_bounds(pr, c + 1) && s->board[pr][c + 1] == W_PAWN) return true;
  } else {
    int pr = r - 1;
    if (in_bounds(pr, c - 1) && s->board[pr][c - 1] == B_PAWN) return true;
    if (in_bounds(pr, c + 1) && s->board[pr][c + 1] == B_PAWN) return true;
  }

  /* Knights */
  static const int kdr[8] = { -2,-2,-1,-1, 1, 1, 2, 2 };
  static const int kdc[8] = { -1, 1,-2, 2,-2, 2,-1, 1 };
  for (int i = 0; i < 8; ++i) {
    int rr = r + kdr[i], cc = c + kdc[i];
    if (!in_bounds(rr, cc)) continue;
    uint8_t p = s->board[rr][cc];
    if (by_white ? (p == W_KNIGHT) : (p == B_KNIGHT)) return true;
  }

  /* King (adjacent) */
  for (int dr = -1; dr <= 1; ++dr) {
    for (int dc = -1; dc <= 1; ++dc) {
      if (dr == 0 && dc == 0) continue;
      int rr = r + dr, cc = c + dc;
      if (!in_bounds(rr, cc)) continue;
      uint8_t p = s->board[rr][cc];
      if (by_white ? (p == W_KING) : (p == B_KING)) return true;
    }
  }

  /* Rook/Queen rays (orthogonal) */
  static const int rdir[4] = { -1, 1, 0, 0 };
  static const int cdir[4] = { 0, 0, -1, 1 };
  for (int d = 0; d < 4; ++d) {
    int rr = r + rdir[d], cc = c + cdir[d];
    for (int step = 1; step < 8 && in_bounds(rr, cc); ++step, rr += rdir[d], cc += cdir[d]) {
      uint8_t p = s->board[rr][cc];
      if (p != EMPTY) {
        if (by_white ? (p == W_ROOK || p == W_QUEEN) : (p == B_ROOK || p == B_QUEEN))
          return true;
        break;
      }
    }
  }

  /* Bishop/Queen rays (diagonals) */
  static const int bdr[4] = { -1, -1, 1, 1 };
  static const int bdc[4] = { -1,  1,-1, 1 };
  for (int d = 0; d < 4; ++d) {
    int rr = r + bdr[d], cc = c + bdc[d];
    for (int step = 1; step < 8 && in_bounds(rr, cc); ++step, rr += bdr[d], cc += bdc[d]) {
      uint8_t p = s->board[rr][cc];
      if (p != EMPTY) {
        if (by_white ? (p == W_BISHOP || p == W_QUEEN) : (p == B_BISHOP || p == B_QUEEN))
          return true;
        break;
      }
    }
  }

  return false;
}

static bool king_in_check(const ChessState *s, bool white) {
  int kr = -1, kc = -1;
  for (int r = 0; r < 8; ++r) {
    for (int c = 0; c < 8; ++c) {
      uint8_t p = s->board[r][c];
      if (white ? (p == W_KING) : (p == B_KING)) { kr = r; kc = c; break; }
    }
    if (kr != -1) break;
  }
  if (kr == -1) return false; /* king captured already */
  return square_attacked_by(s, kr, kc, !white);
}

/* ==== Move semantics (rules + en-passant + promotion) ==== */

static inline int start_row_for_pawn(bool white) { return white ? 6 : 1; }
static inline int dir_for_pawn(bool white)       { return white ? -1 : 1; }

/* Checks basic piece rule + path clearance + en-passant availability.
   Also checks *own king safety* by making the move on a temporary copy.
   Returns true if legal. If legal, sets:
     - *captured_out to the captured piece code (handles en-passant).
     - *captures_king_out to true if the move captures the opponent king.
     - *promotes_out to true if a pawn is promoted (to queen).
*/
static bool is_legal_move_and_effects(const ChessState *s,
                                      int sr, int sc, int dr, int dc,
                                      uint8_t *captured_out,
                                      bool *captures_king_out,
                                      bool *promotes_out)
{
  *captured_out = EMPTY;
  *captures_king_out = false;
  *promotes_out = false;

  if (!in_bounds(sr, sc) || !in_bounds(dr, dc)) return false;
  if (sr == dr && sc == dc) return false;

  uint8_t mover = s->board[sr][sc];
  if (mover == EMPTY) return false;

  bool white_to_move = s->white_to_move != 0u;
  if (white_to_move ? !is_white_piece(mover) : !is_black_piece(mover))
    return false;

  uint8_t target = s->board[dr][dc];
  if (same_color(mover, target)) return false;

  int mt = piece_type(mover);
  int drow = dr - sr, dcol = dc - sc;

  /* Basic movement legality (ignores king safety for now) */
  switch (mt) {
    case 1: { /* Pawn */
      int dir = dir_for_pawn(white_to_move);
      int start_row = start_row_for_pawn(white_to_move);

      /* Simple forward move */
      if (dcol == 0 && drow == dir && target == EMPTY) {
        /* ok */
      }
      /* Double push from starting rank */
      else if (dcol == 0 && drow == 2*dir && sr == start_row) {
        int midr = sr + dir;
        if (s->board[midr][sc] != EMPTY || target != EMPTY) return false;
      }
      /* Diagonal capture */
      else if ((dcol == 1 || dcol == -1) && drow == dir) {
        if (target != EMPTY) {
          /* normal capture */
        } else {
          /* en-passant capture to (dr,dc)? */
          if (!(s->ep_row == dr && s->ep_col == dc)) return false;
          /* Must be capturing a pawn that just moved 2 and sits behind (dr - dir, dc) */
          int cap_r = dr - dir, cap_c = dc;
          if (!in_bounds(cap_r, cap_c)) return false;
          uint8_t behind = s->board[cap_r][cap_c];
          if (white_to_move ? (behind != B_PAWN) : (behind != W_PAWN)) return false;
          *captured_out = behind;
        }
      } else {
        return false;
      }

      /* Promotion? */
      if ((white_to_move && dr == 0) || (!white_to_move && dr == 7)) {
        *promotes_out = true;
      }
    } break;

    case 2: { /* Knight */
      int ar = drow < 0 ? -drow : drow;
      int ac = dcol < 0 ? -dcol : dcol;
      if (!((ar == 2 && ac == 1) || (ar == 1 && ac == 2))) return false;
    } break;

    case 3: { /* Bishop - diagonal, clear path */
      int ar = drow < 0 ? -drow : drow;
      int ac = dcol < 0 ? -dcol : dcol;
      if (ar != ac) return false;
      int stepr = (drow > 0) - (drow < 0);
      int stepc = (dcol > 0) - (dcol < 0);
      for (int step = 1; step < 8; ++step) {
        int rr = sr + stepr * step;
        int cc = sc + stepc * step;
        if (rr == dr && cc == dc) break;
        if (!in_bounds(rr, cc) || s->board[rr][cc] != EMPTY) return false;
      }
    } break;

    case 4: { /* Rook - orthogonal, clear path */
      if (!(drow == 0 || dcol == 0)) return false;
      int stepr = (drow > 0) - (drow < 0);
      int stepc = (dcol > 0) - (dcol < 0);
      for (int step = 1; step < 8; ++step) {
        int rr = sr + stepr * step;
        int cc = sc + stepc * step;
        if (rr == dr && cc == dc) break;
        if (!in_bounds(rr, cc) || s->board[rr][cc] != EMPTY) return false;
      }
    } break;

    case 5: { /* Queen = rook or bishop */
      bool rook_like = (drow == 0 || dcol == 0);
      bool bishop_like = ((drow < 0 ? -drow : drow) == (dcol < 0 ? -dcol : dcol));
      if (!rook_like && !bishop_like) return false;
      int stepr = (drow > 0) - (drow < 0);
      int stepc = (dcol > 0) - (dcol < 0);
      for (int step = 1; step < 8; ++step) {
        int rr = sr + stepr * step;
        int cc = sc + stepc * step;
        if (rr == dr && cc == dc) break;
        if (!in_bounds(rr, cc) || s->board[rr][cc] != EMPTY) return false;
      }
    } break;

    case 6: { /* King (no castling) */
      int ar = drow < 0 ? -drow : drow;
      int ac = dcol < 0 ? -dcol : dcol;
      if (ar > 1 || ac > 1) return false;
    } break;

    default:
      return false;
  }

  /* Compute captured piece for normal captures if not already set (en-passant set it). */
  if (*captured_out == EMPTY && target != EMPTY) {
    *captured_out = target;
  }

  /* Tentatively apply the move on a copy to check king safety. */
  ChessState tmp = *s;

  /* Handle en-passant capture removal if needed. */
  bool is_ep = false;
  if (piece_type(mover) == 1 && target == EMPTY && sc != dc) {
    /* If diagonal pawn move to empty square, it's en-passant (already validated above). */
    if (s->ep_row == dr && s->ep_col == dc) {
      is_ep = true;
      int dir = dir_for_pawn(white_to_move);
      int cap_r = dr - dir, cap_c = dc;
      tmp.board[cap_r][cap_c] = EMPTY;
    }
  }

  /* Move the piece. */
  tmp.board[dr][dc] = mover;
  tmp.board[sr][sc] = EMPTY;

  /* Promotion: always promote to Queen (simple, deterministic). */
  if (*promotes_out) {
    tmp.board[dr][dc] = white_to_move ? W_QUEEN : B_QUEEN;
  }

  /* Update en-passant square for the *next* player. Default: none. */
  tmp.ep_row = -1; tmp.ep_col = -1;
  if (piece_type(mover) == 1 && dcol == 0) {
    int dir = dir_for_pawn(white_to_move);
    if (drow == 2*dir) {
      /* Set the square jumped over. */
      tmp.ep_row = sr + dir;
      tmp.ep_col = sc;
    }
  }

  /* Flip side to move. */
  tmp.white_to_move = white_to_move ? 0u : 1u;

  /* Did we capture the opponent king? */
  if (*captured_out == (white_to_move ? B_KING : W_KING)) {
    *captures_king_out = true;
    return true; /* legal; terminal in our simple model */
  }

  /* Own king must not be in check after the move. */
  if (king_in_check(&tmp, white_to_move)) {
    return false;
  }

  return true;
}

/* Applies an already-validated move to the actual state (mirrors the logic above).
   Returns true if this move captured the opponent king (terminal in this model).
*/
static bool apply_move(ChessState *s, int sr, int sc, int dr, int dc) {
  uint8_t mover = s->board[sr][sc];
  uint8_t target = s->board[dr][dc];
  bool white_to_move = s->white_to_move != 0u;
  bool captured_king = (target == (white_to_move ? B_KING : W_KING));

  /* en-passant removal if needed */
  bool is_ep = false;
  if (piece_type(mover) == 1 && target == EMPTY && sc != dc && s->ep_row == dr && s->ep_col == dc) {
    is_ep = true;
    int dir = dir_for_pawn(white_to_move);
    int cap_r = dr - dir, cap_c = dc;
    if (in_bounds(cap_r, cap_c)) {
      if (white_to_move ? (s->board[cap_r][cap_c] == B_PAWN)
                        : (s->board[cap_r][cap_c] == W_PAWN)) {
        if (s->board[cap_r][cap_c] == (white_to_move ? B_KING : W_KING)) captured_king = true; /* (theoretically impossible) */
        s->board[cap_r][cap_c] = EMPTY;
      }
    }
  }

  /* Move */
  s->board[dr][dc] = mover;
  s->board[sr][sc] = EMPTY;

  /* Promotion to Queen. */
  if (piece_type(mover) == 1 && ((white_to_move && dr == 0) || (!white_to_move && dr == 7))) {
    s->board[dr][dc] = white_to_move ? W_QUEEN : B_QUEEN;
  }

  /* Update en-passant square. */
  s->ep_row = -1; s->ep_col = -1;
  if (piece_type(mover) == 1 && (dc == sc)) {
    int dir = dir_for_pawn(white_to_move);
    if (dr - sr == 2*dir) {
      s->ep_row = sr + dir;
      s->ep_col = sc;
    }
  }

  /* Flip side to move. */
  s->white_to_move = white_to_move ? 0u : 1u;

  return captured_king;
}

/* Material difference S0 = (White material) - (Black material). */
static int material_diff_white_minus_black(const ChessState *s) {
  int sum = 0;
  for (int r = 0; r < 8; ++r) {
    for (int c = 0; c < 8; ++c) {
      uint8_t pc = s->board[r][c];
      if (pc == EMPTY) continue;
      int v = value_of_piece_code(pc);
      sum += is_white_piece(pc) ? v : -v;
    }
  }
  return sum;
}

/* Deterministically choose the best legal move for the side to move IF that side is the root side.
   Scoring is purely material delta from the root player's perspective (white-minus-black sign-flipped if root is Black).
   No recursion, no lookahead beyond one ply (the nondet opponent move happens after this).
*/
static bool choose_best_move_one_ply(const ChessState *s, bool root_white,
                                     uint16_t *best_code_out, bool *best_is_terminal_out)
{
  *best_is_terminal_out = false;
  int baseS0 = material_diff_white_minus_black(s);
  int rootSign = root_white ? 1 : -1;

  int bestScore = -2147483647; /* -INF */
  uint16_t bestCode = 0;
  bool found = false;

  /* Scan board once; generate moves piece-by-piece (limits nested loops). */
  for (int sr = 0; sr < 8; ++sr) {
    for (int sc = 0; sc < 8; ++sc) {
      uint8_t mover = s->board[sr][sc];
      if (mover == EMPTY) continue;
      if (root_white ? !is_white_piece(mover) : !is_black_piece(mover)) continue;

      int mt = piece_type(mover);
      bool white_to_move = s->white_to_move != 0u;
      /* Sanity: this function should only be called when side to move == root side. */
      if (white_to_move != root_white) continue;

      /* Candidate destinations, by piece type. Keep it flat and bounded. */
      if (mt == 1) {
        int dir = dir_for_pawn(white_to_move);
        int start_row = start_row_for_pawn(white_to_move);

        /* Single step */
        int dr = sr + dir, dc = sc;
        if (in_bounds(dr, dc) && s->board[dr][dc] == EMPTY) {
          uint8_t cap; bool ck, promo;
          if (is_legal_move_and_effects(s, sr, sc, dr, dc, &cap, &ck, &promo)) {
            int deltaS0 = promo ? (white_to_move ? +800 : -800) : 0; /* Q(900)-P(100)=800 */
            int score = rootSign * (baseS0 + deltaS0);
            if (!found || score > bestScore) { found = true; bestScore = score; bestCode = encode12(sr, sc, dr, dc); *best_is_terminal_out = ck; }
            if (ck) { *best_code_out = bestCode; return true; }
          }
        }
        /* Double step */
        dr = sr + 2*dir; dc = sc;
        if (sr == start_row && in_bounds(dr, dc) && s->board[sr + dir][dc] == EMPTY && s->board[dr][dc] == EMPTY) {
          uint8_t cap; bool ck, promo;
          if (is_legal_move_and_effects(s, sr, sc, dr, dc, &cap, &ck, &promo)) {
            int score = rootSign * (baseS0);
            if (!found || score > bestScore) { found = true; bestScore = score; bestCode = encode12(sr, sc, dr, dc); *best_is_terminal_out = ck; }
            if (ck) { *best_code_out = bestCode; return true; }
          }
        }
        /* Captures (including en-passant) */
        for (int dc_off = -1; dc_off <= 1; dc_off += 2) {
          dr = sr + dir; dc = sc + dc_off;
          if (!in_bounds(dr, dc)) continue;
          uint8_t cap0 = s->board[dr][dc];
          /* Allow diagonal to empty only if en-passant square matches. */
          if (cap0 == EMPTY && !(s->ep_row == dr && s->ep_col == dc)) {
            /* illegal candidate; skip */
          } else {
            uint8_t cap; bool ck, promo;
            if (is_legal_move_and_effects(s, sr, sc, dr, dc, &cap, &ck, &promo)) {
              int vcap = value_of_piece_code(cap);
              int deltaS0 = (white_to_move ? +vcap : -vcap) + (promo ? (white_to_move ? +800 : -800) : 0);
              int score = rootSign * (baseS0 + deltaS0);
              if (!found || score > bestScore) { found = true; bestScore = score; bestCode = encode12(sr, sc, dr, dc); *best_is_terminal_out = ck; }
              if (ck) { *best_code_out = bestCode; return true; }
            }
          }
        }
      } else if (mt == 2) {
        static const int kdr[8] = { -2,-2,-1,-1, 1, 1, 2, 2 };
        static const int kdc[8] = { -1, 1,-2, 2,-2, 2,-1, 1 };
        for (int i = 0; i < 8; ++i) {
          int dr = sr + kdr[i], dc = sc + kdc[i];
          if (!in_bounds(dr, dc)) continue;
          if (same_color(mover, s->board[dr][dc])) continue;
          uint8_t cap; bool ck, promo;
          if (is_legal_move_and_effects(s, sr, sc, dr, dc, &cap, &ck, &promo)) {
            int vcap = value_of_piece_code(cap);
            int deltaS0 = white_to_move ? +vcap : -vcap;
            int score = rootSign * (baseS0 + deltaS0);
            if (!found || score > bestScore) { found = true; bestScore = score; bestCode = encode12(sr, sc, dr, dc); *best_is_terminal_out = ck; }
            if (ck) { *best_code_out = bestCode; return true; }
          }
        }
      } else if (mt == 3 || mt == 4 || mt == 5) {
        /* Sliding pieces: pick directions based on type. */
        int dirs_r[8], dirs_c[8], nd = 0;
        if (mt == 3 || mt == 5) { /* bishop-like diagonals */
          dirs_r[nd] = -1; dirs_c[nd++] = -1;
          dirs_r[nd] = -1; dirs_c[nd++] =  1;
          dirs_r[nd] =  1; dirs_c[nd++] = -1;
          dirs_r[nd] =  1; dirs_c[nd++] =  1;
        }
        if (mt == 4 || mt == 5) { /* rook-like orthogonals */
          dirs_r[nd] = -1; dirs_c[nd++] =  0;
          dirs_r[nd] =  1; dirs_c[nd++] =  0;
          dirs_r[nd] =  0; dirs_c[nd++] = -1;
          dirs_r[nd] =  0; dirs_c[nd++] =  1;
        }
        for (int d = 0; d < nd; ++d) {
          int rr = sr + dirs_r[d], cc = sc + dirs_c[d];
          for (int step = 1; step < 8 && in_bounds(rr, cc); ++step, rr += dirs_r[d], cc += dirs_c[d]) {
            uint8_t dst = s->board[rr][cc];
            if (same_color(mover, dst)) break;
            uint8_t cap; bool ck, promo;
            if (is_legal_move_and_effects(s, sr, sc, rr, cc, &cap, &ck, &promo)) {
              int vcap = value_of_piece_code(cap);
              int deltaS0 = white_to_move ? +vcap : -vcap;
              int score = rootSign * (baseS0 + deltaS0);
              if (!found || score > bestScore) { found = true; bestScore = score; bestCode = encode12(sr, sc, rr, cc); *best_is_terminal_out = ck; }
              if (ck) { *best_code_out = bestCode; return true; }
            }
            if (dst != EMPTY) break; /* cannot go past a capture */
          }
        }
      } else if (mt == 6) {
        for (int dr = sr - 1; dr <= sr + 1; ++dr) {
          for (int dc = sc - 1; dc <= sc + 1; ++dc) {
            if (dr == sr && dc == sc) continue;
            if (!in_bounds(dr, dc)) continue;
            if (same_color(mover, s->board[dr][dc])) continue;
            uint8_t cap; bool ck, promo;
            if (is_legal_move_and_effects(s, sr, sc, dr, dc, &cap, &ck, &promo)) {
              int vcap = value_of_piece_code(cap);
              int deltaS0 = white_to_move ? +vcap : -vcap;
              int score = rootSign * (baseS0 + deltaS0);
              if (!found || score > bestScore) { found = true; bestScore = score; bestCode = encode12(sr, sc, dr, dc); *best_is_terminal_out = ck; }
              if (ck) { *best_code_out = bestCode; return true; }
            }
          }
        }
      }
    }
  }

  if (!found) return false;
  *best_code_out = bestCode;
  return true;
}

/* === Public driver: play forward up to MAX_DEPTH plies ===
   Root player (the one to move initially) plays best moves; the opponent plays nondet legal moves.
   Each move (deterministic or nondet) is stored as a 12-bit code in moves_out[].
   Stops early if a king is captured.
*/
#ifndef MAX_DEPTH
#define MAX_DEPTH 4
#endif

static uint16_t g_played_moves[MAX_DEPTH];
static int      g_num_played = 0;

/* Expose them so CBMC can observe. */
uint16_t const *chessengine_moves_ptr(void) { return g_played_moves; }
int chessengine_moves_len(void) { return g_num_played; }

/* Main engine stepper */
void play_to_depth(ChessState *s, int depth) {
  if (depth > MAX_DEPTH) depth = MAX_DEPTH;

  g_num_played = 0;
  bool root_white = s->white_to_move != 0u;

  for (int ply = 0; ply < depth; ++ply) {
    bool white_to_move = s->white_to_move != 0u;

    if (white_to_move == root_white) {
      /* Deterministic best move for root side */
      uint16_t code = 0; bool terminal = false;
      bool ok = choose_best_move_one_ply(s, root_white, &code, &terminal);
      if (!ok) break; /* no legal moves (treated as stop) */
      int sr, sc, dr, dc; decode12(code, &sr, &sc, &dr, &dc);
      /* Re-validate is optional since chooser already validated; kept consistent for safety. */
      uint8_t cap; bool ck, promo;
      bool legal = is_legal_move_and_effects(s, sr, sc, dr, dc, &cap, &ck, &promo);
      if (!legal) break;
      bool ends = apply_move(s, sr, sc, dr, dc);
      g_played_moves[g_num_played++] = code;
      if (ends || terminal) break;
    } else {
      /* Opponent: nondeterministic legal 12-bit move */
      uint16_t code = nondet_uint16_t() % 4096u;
      int sr, sc, dr, dc; decode12(code, &sr, &sc, &dr, &dc);
      uint8_t cap; bool ck, promo;
      bool legal = is_legal_move_and_effects(s, sr, sc, dr, dc, &cap, &ck, &promo);
      __CPROVER_assume(legal); /* prune illegal nondet choices */
      bool ends = apply_move(s, sr, sc, dr, dc);
      g_played_moves[g_num_played++] = code;
      if (ends) break;
    }
  }
}

#include <stdio.h>
int main(void) {
  play_to_depth(&g_state, MAX_DEPTH);
  printf("Plies played: %d\n", g_num_played);
  for (int i = 0; i < g_num_played; ++i) {
    int sr, sc, dr, dc; decode12(g_played_moves[i], &sr, &sc, &dr, &dc);
    printf("%d: (%d,%d)->(%d,%d)\n", i+1, sr, sc, dr, dc);
  }
  return 0;
}
