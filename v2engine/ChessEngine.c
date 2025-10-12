#include <stdint.h>
#include <stdbool.h>
#include "ChessState.h"

/* === CBMC integration === */
extern uint16_t nondet_uint16_t(void);
void __CPROVER_assume(_Bool);

/* Make __CPROVER_unwind a no-op outside CBMC. */
#ifndef __CPROVER_unwind
#define __CPROVER_unwind(...) /* nothing */
#endif

/* ===== Move encoding: 12 bits total =====
   bits: 0..2=srcRow, 3..5=srcCol, 6..8=dstRow, 9..11=dstCol  (0..4095)
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

static inline int value_of_piece_code(uint8_t pc) {
  return PIECE_VALUE_BY_TYPE[piece_type(pc)];
}
static inline int same_color(uint8_t a, uint8_t b) {
  if (a == EMPTY || b == EMPTY) return 0;
  return (is_white_piece(a) && is_white_piece(b)) || (is_black_piece(a) && is_black_piece(b));
}

/* === Attack detection ===
   We removed the 8x8 king scan (king coords are stored in the state).
   We also cap/unwind ray walks to 7 steps for CBMC.
*/
static bool square_attacked_by(const ChessState *s, int r, int c, bool by_white) {
  /* Pawns: if square (r,c) is attacked by a white pawn, such a pawn must be at (r+1,c±1);
     for black, at (r-1,c±1). */
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

  /* Orthogonal rays: Rooks/Queens */
  {
    int rr = r, cc = c;
    /* up (-1,0) */
    rr = r; cc = c;
    for (int step = 1; step <= 7; ++step) {
      rr -= 1;
      if (!in_bounds(rr, cc)) break;
      uint8_t p = s->board[rr][cc];
      if (p != EMPTY) { if (by_white ? (p==W_ROOK||p==W_QUEEN) : (p==B_ROOK||p==B_QUEEN)) return true; else break; }
    }
    /* down (+1,0) */
    rr = r; cc = c;
    for (int step = 1; step <= 7; ++step) {
      rr += 1;
      if (!in_bounds(rr, cc)) break;
      uint8_t p = s->board[rr][cc];
      if (p != EMPTY) { if (by_white ? (p==W_ROOK||p==W_QUEEN) : (p==B_ROOK||p==B_QUEEN)) return true; else break; }
    }
    /* left (0,-1) */
    rr = r; cc = c;
    for (int step = 1; step <= 7; ++step) {
      cc -= 1;
      if (!in_bounds(rr, cc)) break;
      uint8_t p = s->board[rr][cc];
      if (p != EMPTY) { if (by_white ? (p==W_ROOK||p==W_QUEEN) : (p==B_ROOK||p==B_QUEEN)) return true; else break; }
    }
    /* right (0,+1) */
    rr = r; cc = c;
    for (int step = 1; step <= 7; ++step) {
      cc += 1;
      if (!in_bounds(rr, cc)) break;
      uint8_t p = s->board[rr][cc];
      if (p != EMPTY) { if (by_white ? (p==W_ROOK||p==W_QUEEN) : (p==B_ROOK||p==B_QUEEN)) return true; else break; }
    }
  }

  /* Diagonal rays: Bishops/Queens */
  {
    int rr = r, cc = c;
    /* up-left (-1,-1) */
    rr = r; cc = c;
    for (int step = 1; step <= 7; ++step) {
      rr -= 1; cc -= 1;
      if (!in_bounds(rr, cc)) break;
      uint8_t p = s->board[rr][cc];
      if (p != EMPTY) { if (by_white ? (p==W_BISHOP||p==W_QUEEN) : (p==B_BISHOP||p==B_QUEEN)) return true; else break; }
    }
    /* up-right (-1,+1) */
    rr = r; cc = c;

    for (int step = 1; step <= 7; ++step) {
      rr -= 1; cc += 1;
      if (!in_bounds(rr, cc)) break;
      uint8_t p = s->board[rr][cc];
      if (p != EMPTY) { if (by_white ? (p==W_BISHOP||p==W_QUEEN) : (p==B_BISHOP||p==B_QUEEN)) return true; else break; }
    }
    /* down-left (+1,-1) */
    rr = r; cc = c;

    for (int step = 1; step <= 7; ++step) {
      rr += 1; cc -= 1;
      if (!in_bounds(rr, cc)) break;
      uint8_t p = s->board[rr][cc];
      if (p != EMPTY) { if (by_white ? (p==W_BISHOP||p==W_QUEEN) : (p==B_BISHOP||p==B_QUEEN)) return true; else break; }
    }
    /* down-right (+1,+1) */
    rr = r; cc = c;

    for (int step = 1; step <= 7; ++step) {
      rr += 1; cc += 1;
      if (!in_bounds(rr, cc)) break;
      uint8_t p = s->board[rr][cc];
      if (p != EMPTY) { if (by_white ? (p==W_BISHOP||p==W_QUEEN) : (p==B_BISHOP||p==B_QUEEN)) return true; else break; }
    }
  }

  return false;
}

static inline bool king_in_check(const ChessState *s, bool white) {
  int kr = white ? s->w_king_r : s->b_king_r;
  int kc = white ? s->w_king_c : s->b_king_c;
  if (kr < 0 || kc < 0) return true; /* king missing -> treat as bad/checked */
  return square_attacked_by(s, kr, kc, !white);
}

/* ==== Move semantics (rules + en-passant + promotion + castling) ==== */

static inline int start_row_for_pawn(bool white) { return white ? 6 : 1; }
static inline int dir_for_pawn(bool white)       { return white ? -1 : 1; }

static inline void clear_castle_rights_for_color(ChessState *st, bool white) {
  if (white) st->castle_rights &= ~(CR_WK | CR_WQ);
  else       st->castle_rights &= ~(CR_BK | CR_BQ);
}

static inline void clear_castle_right_for_rook_square(ChessState *st, int r, int c) {
  if (r == 7 && c == 0) st->castle_rights &= ~CR_WQ;
  if (r == 7 && c == 7) st->castle_rights &= ~CR_WK;
  if (r == 0 && c == 0) st->castle_rights &= ~CR_BQ;
  if (r == 0 && c == 7) st->castle_rights &= ~CR_BK;
}

/* Checks piece rules, path clearance, en-passant, castling, and own-king safety.
   Returns true if legal. If legal, sets:
     - *captured_out to captured piece (handles en-passant).
     - *promotes_out if pawn promotes (to queen).
*/
static bool is_legal_move_and_effects(const ChessState *s,
                                      int sr, int sc, int dr, int dc,
                                      uint8_t *captured_out,
                                      bool *promotes_out)
{
  *captured_out = EMPTY;
  *promotes_out = false;

  if (!in_bounds(sr, sc) || !in_bounds(dr, dc)) return false;
  if (sr == dr && sc == dc) return false;

  uint8_t mover = s->board[sr][sc];
  if (mover == EMPTY) return false;

  bool white_to_move = s->white_to_move != 0u;
  if (white_to_move ? !is_white_piece(mover) : !is_black_piece(mover)) return false;

  uint8_t target = s->board[dr][dc];
  if (same_color(mover, target)) return false;

  /* You cannot capture the opponent's king; checkmate ends the game before that. */
  if (target == (white_to_move ? B_KING : W_KING)) return false;

  int mt = piece_type(mover);
  int drow = dr - sr, dcol = dc - sc;

  bool is_castle = false;
  bool castle_kingside = false;

  /* Basic movement legality (ignores king safety for now) */
  switch (mt) {
    case 1: { /* Pawn */
      int dir = dir_for_pawn(white_to_move);
      int start_row = start_row_for_pawn(white_to_move);

      /* Single forward */
      if (dcol == 0 && drow == dir && target == EMPTY) {
        /* ok */
      }
      /* Double from start */
      else if (dcol == 0 && drow == 2*dir && sr == start_row) {
        int midr = sr + dir;
        if (s->board[midr][sc] != EMPTY || target != EMPTY) return false;
      }
      /* Diagonal capture or en-passant */
      else if ((dcol == 1 || dcol == -1) && drow == dir) {
        if (target != EMPTY) {
          /* normal capture */
        } else {
          if (!(s->ep_row == dr && s->ep_col == dc)) return false;
          int cap_r = dr - dir, cap_c = dc;
          if (!in_bounds(cap_r, cap_c)) return false;
          uint8_t behind = s->board[cap_r][cap_c];
          if (white_to_move ? (behind != B_PAWN) : (behind != W_PAWN)) return false;
          *captured_out = behind;
        }
      } else return false;

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

    case 3: { /* Bishop */
      int ar = drow < 0 ? -drow : drow;
      int ac = dcol < 0 ? -dcol : dcol;
      if (ar != ac) return false;
      int stepr = (drow > 0) - (drow < 0);
      int stepc = (dcol > 0) - (dcol < 0);

      for (int step = 1; step < 8; ++step) {
        int rr = sr + stepr * step, cc = sc + stepc * step;
        if (rr == dr && cc == dc) break;
        if (!in_bounds(rr, cc) || s->board[rr][cc] != EMPTY) return false;
      }
    } break;

    case 4: { /* Rook */
      if (!(drow == 0 || dcol == 0)) return false;
      int stepr = (drow > 0) - (drow < 0);
      int stepc = (dcol > 0) - (dcol < 0);

      for (int step = 1; step < 8; ++step) {
        int rr = sr + stepr * step, cc = sc + stepc * step;
        if (rr == dr && cc == dc) break;
        if (!in_bounds(rr, cc) || s->board[rr][cc] != EMPTY) return false;
      }
    } break;

    case 5: { /* Queen */
      bool rook_like = (drow == 0 || dcol == 0);
      bool bishop_like = ((drow < 0 ? -drow : drow) == (dcol < 0 ? -dcol : dcol));
      if (!rook_like && !bishop_like) return false;
      int stepr = (drow > 0) - (drow < 0);
      int stepc = (dcol > 0) - (dcol < 0);

      for (int step = 1; step < 8; ++step) {
        int rr = sr + stepr * step, cc = sc + stepc * step;
        if (rr == dr && cc == dc) break;
        if (!in_bounds(rr, cc) || s->board[rr][cc] != EMPTY) return false;
      }
    } break;

    case 6: { /* King (+castling) */
      int ar = drow < 0 ? -drow : drow;
      int ac = dcol < 0 ? -dcol : dcol;

      /* Standard king move (no castling) */
      if (ar <= 1 && ac <= 1 && !(ar == 0 && ac == 0)) {
        /* ok */
      }
      /* Castling: same row, move two columns */
      else if (ar == 0 && ac == 2) {
        bool white = white_to_move;
        bool kingside = (dcol == 2);
        int row = sr;
        int rook_c_from = kingside ? 7 : 0;
        int rook_c_to   = kingside ? 5 : 3;
        /* Rights + pieces on original squares */
        if (white) {
          if (kingside && !(s->castle_rights & CR_WK)) return false;
          if (!kingside && !(s->castle_rights & CR_WQ)) return false;
          if (sr != 7 || sc != 4) return false;
          if (s->board[row][rook_c_from] != W_ROOK) return false;
        } else {
          if (kingside && !(s->castle_rights & CR_BK)) return false;
          if (!kingside && !(s->castle_rights & CR_BQ)) return false;
          if (sr != 0 || sc != 4) return false;
          if (s->board[row][rook_c_from] != B_ROOK) return false;
        }
        /* Squares between king and rook must be empty */
        int c1 = sc + (kingside ? 1 : -1);
        int c2 = sc + (kingside ? 2 : -2);
        if (s->board[row][c1] != EMPTY || s->board[row][c2] != EMPTY) return false;
        if (!kingside) {
          int c3 = sc - 3;
          if (s->board[row][c3] != EMPTY) return false; /* b-file must also be empty */
        }
        /* King cannot be in check, nor pass through an attacked square, nor end in check */
        if (king_in_check(s, white)) return false;
        if (square_attacked_by(s, row, c1, !white)) return false;
        if (square_attacked_by(s, row, c2, !white)) return false;

        is_castle = true;
        castle_kingside = kingside;
      } else return false;
    } break;

    default: return false;
  }

  /* Captured piece for normal captures if not set (en-passant already set it). */
  if (*captured_out == EMPTY && target != EMPTY) *captured_out = target;

  /* Simulate move to check king safety and to update king location/rights. */
  ChessState tmp = *s;

  /* En-passant removal if needed */
  if (piece_type(mover) == 1 && target == EMPTY && sc != dc) {
    if (s->ep_row == dr && s->ep_col == dc) {
      int dir = dir_for_pawn(white_to_move);
      int cap_r = dr - dir, cap_c = dc;
      tmp.board[cap_r][cap_c] = EMPTY;
    }
  }

  /* Move (and potentially castle rook) */
  tmp.board[dr][dc] = mover;
  tmp.board[sr][sc] = EMPTY;

  /* Promotion -> queen */
  if (*promotes_out) tmp.board[dr][dc] = white_to_move ? W_QUEEN : B_QUEEN;

  /* Update en-passant */
  tmp.ep_row = -1; tmp.ep_col = -1;
  if (piece_type(mover) == 1 && dcol == 0) {
    int dir = dir_for_pawn(white_to_move);
    if (drow == 2*dir) { tmp.ep_row = sr + dir; tmp.ep_col = sc; }
  }

  /* Update castling rights/king coords */
  if (piece_type(mover) == 6) {
    clear_castle_rights_for_color(&tmp, white_to_move);
    if (white_to_move) { tmp.w_king_r = dr; tmp.w_king_c = dc; }
    else               { tmp.b_king_r = dr; tmp.b_king_c = dc; }

    if (is_castle) {
      int row = sr;
      int rook_from_c = castle_kingside ? 7 : 0;
      int rook_to_c   = castle_kingside ? 5 : 3;
      uint8_t rook = white_to_move ? W_ROOK : B_ROOK;
      tmp.board[row][rook_to_c] = rook;
      tmp.board[row][rook_from_c] = EMPTY;
    }
  } else {
    /* Moving any rook from its original square revokes that right */
    if (piece_type(mover) == 4) clear_castle_right_for_rook_square(&tmp, sr, sc);
    /* Capturing a rook on its original square revokes opponent right */
    if (*captured_out == W_ROOK) clear_castle_right_for_rook_square(&tmp, dr, dc);
    if (*captured_out == B_ROOK) clear_castle_right_for_rook_square(&tmp, dr, dc);
    /* King coordinates unchanged unless we actually moved the king. */
  }

  /* Flip side to move (not used for the check below, but keep state consistent). */
  tmp.white_to_move = white_to_move ? 0u : 1u;

  /* Own king must not be in check after the move. */
  if (king_in_check(&tmp, white_to_move)) return false;

  return true;
}

/* Applies an already-validated move to the actual state. */
static void apply_move(ChessState *s, int sr, int sc, int dr, int dc) {
  uint8_t mover = s->board[sr][sc];
  uint8_t target = s->board[dr][dc];
  bool white_to_move = s->white_to_move != 0u;

  /* En-passant capture removal */
  if (piece_type(mover) == 1 && target == EMPTY && sc != dc && s->ep_row == dr && s->ep_col == dc) {
    int dir = dir_for_pawn(white_to_move);
    int cap_r = dr - dir, cap_c = dc;
    s->board[cap_r][cap_c] = EMPTY;
  }

  /* Detect castling (king moves two squares) before we overwrite the king square. */
  bool is_king = (piece_type(mover) == 6);
  bool is_castle = is_king && (sr == dr) && ((dc - sc == 2) || (sc - dc == 2));
  bool castle_kingside = is_castle && (dc > sc);

  /* Move the piece */
  s->board[dr][dc] = mover;
  s->board[sr][sc] = EMPTY;

  /* Promotion to Queen */
  if (piece_type(mover) == 1 && ((white_to_move && dr == 0) || (!white_to_move && dr == 7))) {
    s->board[dr][dc] = white_to_move ? W_QUEEN : B_QUEEN;
  }

  /* Update en-passant */
  s->ep_row = -1; s->ep_col = -1;
  if (piece_type(mover) == 1 && (dc == sc)) {
    int dir = dir_for_pawn(white_to_move);
    if (dr - sr == 2*dir) { s->ep_row = sr + dir; s->ep_col = sc; }
  }

  /* Update castling rights & rook motion for castling */
  if (is_king) {
    clear_castle_rights_for_color(s, white_to_move);
    if (white_to_move) { s->w_king_r = dr; s->w_king_c = dc; }
    else               { s->b_king_r = dr; s->b_king_c = dc; }

    if (is_castle) {
      int row = sr;
      int rook_from_c = castle_kingside ? 7 : 0;
      int rook_to_c   = castle_kingside ? 5 : 3;
      uint8_t rook = white_to_move ? W_ROOK : B_ROOK;
      s->board[row][rook_to_c] = rook;
      s->board[row][rook_from_c] = EMPTY;
    }
  } else {
    /* Revoke rook-side rights when rook moves or when a rook is captured on its home square. */
    if (piece_type(mover) == 4) clear_castle_right_for_rook_square(s, sr, sc);
    if (target == W_ROOK) clear_castle_right_for_rook_square(s, dr, dc);
    if (target == B_ROOK) clear_castle_right_for_rook_square(s, dr, dc);
  }

  /* Flip side to move */
  s->white_to_move = white_to_move ? 0u : 1u;
}

/* Material evaluation: (White material) - (Black material). */
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

/* ---- Move existence test (for mate/stalemate and for nondet side) ---- */
static bool exists_any_legal_move(const ChessState *s) {
  bool side_white = s->white_to_move != 0u;

  for (int sr = 0; sr < 8; ++sr) {
    for (int sc = 0; sc < 8; ++sc) {
      uint8_t mover = s->board[sr][sc];
      if (mover == EMPTY) continue;
      if (side_white ? !is_white_piece(mover) : !is_black_piece(mover)) continue;

      int mt = piece_type(mover);

      if (mt == 1) { /* Pawn: up to 4 targets */
        int dir = dir_for_pawn(side_white);
        int start_row = start_row_for_pawn(side_white);
        int dr = sr + dir, dc = sc;
        if (in_bounds(dr, dc) && s->board[dr][dc] == EMPTY) {
          uint8_t cap; bool promo;
          if (is_legal_move_and_effects(s, sr, sc, dr, dc, &cap, &promo)) return true;
        }
        dr = sr + 2*dir; dc = sc;
        if (sr == start_row && in_bounds(dr, dc) && s->board[sr + dir][dc] == EMPTY && s->board[dr][dc] == EMPTY) {
          uint8_t cap; bool promo;
          if (is_legal_move_and_effects(s, sr, sc, dr, dc, &cap, &promo)) return true;
        }
        for (int off = -1; off <= 1; off += 2) {
          dr = sr + dir; dc = sc + off;
          if (!in_bounds(dr, dc)) continue;
          uint8_t cap; bool promo;
          /* Allow diag to empty only if en-passant square matches; is_legal will reject otherwise anyway. */
          if (is_legal_move_and_effects(s, sr, sc, dr, dc, &cap, &promo)) return true;
        }
      } else if (mt == 2) { /* Knight */
        static const int kdr[8] = { -2,-2,-1,-1, 1, 1, 2, 2 };
        static const int kdc[8] = { -1, 1,-2, 2,-2, 2,-1, 1 };
        for (int i = 0; i < 8; ++i) {
          int dr = sr + kdr[i], dc = sc + kdc[i];
          if (!in_bounds(dr, dc)) continue;
          if (same_color(mover, s->board[dr][dc])) continue;
          uint8_t cap; bool promo;
          if (is_legal_move_and_effects(s, sr, sc, dr, dc, &cap, &promo)) return true;
        }
      } else if (mt == 3 || mt == 4 || mt == 5) { /* Sliders */
        int dirs_r[8], dirs_c[8], nd = 0;
        if (mt == 3 || mt == 5) { /* bishop-like */
          dirs_r[nd] = -1; dirs_c[nd++] = -1;
          dirs_r[nd] = -1; dirs_c[nd++] =  1;
          dirs_r[nd] =  1; dirs_c[nd++] = -1;
          dirs_r[nd] =  1; dirs_c[nd++] =  1;
        }
        if (mt == 4 || mt == 5) { /* rook-like */
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
            uint8_t cap; bool promo;
            if (is_legal_move_and_effects(s, sr, sc, rr, cc, &cap, &promo)) return true;
            if (dst != EMPTY) break;
          }
        }
      } else if (mt == 6) { /* King */
        for (int dr = sr - 1; dr <= sr + 1; ++dr) {
          for (int dc = sc - 1; dc <= sc + 1; ++dc) {
            if (dr == sr && dc == sc) continue;
            if (!in_bounds(dr, dc)) continue;
            if (same_color(mover, s->board[dr][dc])) continue;
            uint8_t cap; bool promo;
            if (is_legal_move_and_effects(s, sr, sc, dr, dc, &cap, &promo)) return true;
          }
        }
        /* Castling attempts: try both destinations explicitly; is_legal handles details. */
        if (sr == (side_white ? 7 : 0) && sc == 4) {
          int dest_k = 6, dest_q = 2;
          uint8_t cap; bool promo;
          if (is_legal_move_and_effects(s, sr, sc, sr, dest_k, &cap, &promo)) return true;
          if (is_legal_move_and_effects(s, sr, sc, sr, dest_q, &cap, &promo)) return true;
        }
      }
    }
  }
  return false;
}

/* Deterministically choose the best legal move for the root side (one ply).
   Score = material delta (root perspective). Castling gets a tiny bonus (+30) to break ties.
*/
static bool choose_best_move_one_ply(const ChessState *s, bool root_white,
                                     uint16_t *best_code_out)
{
  int baseS0 = material_diff_white_minus_black(s);
  int rootSign = root_white ? 1 : -1;

  int bestScore = -2147483647; /* -INF */
  uint16_t bestCode = 0;
  bool found = false;

  for (int sr = 0; sr < 8; ++sr) {
    for (int sc = 0; sc < 8; ++sc) {
      uint8_t mover = s->board[sr][sc];
      if (mover == EMPTY) continue;
      if (root_white ? !is_white_piece(mover) : !is_black_piece(mover)) continue;

      int mt = piece_type(mover);
      bool white_to_move = s->white_to_move != 0u;
      if (white_to_move != root_white) continue;

      if (mt == 1) {
        int dir = dir_for_pawn(white_to_move);
        int start_row = start_row_for_pawn(white_to_move);

        int dr = sr + dir, dc = sc;
        if (in_bounds(dr, dc) && s->board[dr][dc] == EMPTY) {
          uint8_t cap; bool promo;
          if (is_legal_move_and_effects(s, sr, sc, dr, dc, &cap, &promo)) {
            int deltaS0 = promo ? (white_to_move ? +800 : -800) : 0;
            int score = rootSign * (baseS0 + deltaS0);
            if (!found || score > bestScore) { found = true; bestScore = score; bestCode = encode12(sr, sc, dr, dc); }
          }
        }
        dr = sr + 2*dir; dc = sc;
        if (sr == start_row && in_bounds(dr, dc) && s->board[sr + dir][dc] == EMPTY && s->board[dr][dc] == EMPTY) {
          uint8_t cap; bool promo;
          if (is_legal_move_and_effects(s, sr, sc, dr, dc, &cap, &promo)) {
            int score = rootSign * baseS0;
            if (!found || score > bestScore) { found = true; bestScore = score; bestCode = encode12(sr, sc, dr, dc); }
          }
        }
        for (int off = -1; off <= 1; off += 2) {
          dr = sr + dir; dc = sc + off;
          if (!in_bounds(dr, dc)) continue;
          uint8_t cap; bool promo;
          if (is_legal_move_and_effects(s, sr, sc, dr, dc, &cap, &promo)) {
            int vcap = value_of_piece_code(cap);
            int deltaS0 = (white_to_move ? +vcap : -vcap) + (promo ? (white_to_move ? +800 : -800) : 0);
            int score = rootSign * (baseS0 + deltaS0);
            if (!found || score > bestScore) { found = true; bestScore = score; bestCode = encode12(sr, sc, dr, dc); }
          }
        }
      } else if (mt == 2) {
        static const int kdr[8] = { -2,-2,-1,-1, 1, 1, 2, 2 };
        static const int kdc[8] = { -1, 1,-2, 2,-2, 2,-1, 1 };
        for (int i = 0; i < 8; ++i) {
          int dr = sr + kdr[i], dc = sc + kdc[i];
          if (!in_bounds(dr, dc)) continue;
          if (same_color(mover, s->board[dr][dc])) continue;
          uint8_t cap; bool promo;
          if (is_legal_move_and_effects(s, sr, sc, dr, dc, &cap, &promo)) {
            int vcap = value_of_piece_code(cap);
            int deltaS0 = white_to_move ? +vcap : -vcap;
            int score = rootSign * (baseS0 + deltaS0);
            if (!found || score > bestScore) { found = true; bestScore = score; bestCode = encode12(sr, sc, dr, dc); }
          }
        }
      } else if (mt == 3 || mt == 4 || mt == 5) {
        int dirs_r[8], dirs_c[8], nd = 0;
        if (mt == 3 || mt == 5) { dirs_r[nd] = -1; dirs_c[nd++] = -1; dirs_r[nd] = -1; dirs_c[nd++] =  1;
                                  dirs_r[nd] =  1; dirs_c[nd++] = -1; dirs_r[nd] =  1; dirs_c[nd++] =  1; }
        if (mt == 4 || mt == 5) { dirs_r[nd] = -1; dirs_c[nd++] =  0; dirs_r[nd] =  1; dirs_c[nd++] =  0;
                                  dirs_r[nd] =  0; dirs_c[nd++] = -1; dirs_r[nd] =  0; dirs_c[nd++] =  1; }
        for (int d = 0; d < nd; ++d) {
          int rr = sr + dirs_r[d], cc = sc + dirs_c[d];

          for (int step = 1; step < 8 && in_bounds(rr, cc); ++step, rr += dirs_r[d], cc += dirs_c[d]) {
            uint8_t dst = s->board[rr][cc];
            if (same_color(mover, dst)) break;
            uint8_t cap; bool promo;
            if (is_legal_move_and_effects(s, sr, sc, rr, cc, &cap, &promo)) {
              int vcap = value_of_piece_code(cap);
              int deltaS0 = white_to_move ? +vcap : -vcap;
              int score = rootSign * (baseS0 + deltaS0);
              if (!found || score > bestScore) { found = true; bestScore = score; bestCode = encode12(sr, sc, rr, cc); }
            }
            if (dst != EMPTY) break;
          }
        }
      } else if (mt == 6) {
        for (int dr = sr - 1; dr <= sr + 1; ++dr) {
          for (int dc = sc - 1; dc <= sc + 1; ++dc) {
            if (dr == sr && dc == sc) continue;
            if (!in_bounds(dr, dc)) continue;
            if (same_color(mover, s->board[dr][dc])) continue;
            uint8_t cap; bool promo;
            if (is_legal_move_and_effects(s, sr, sc, dr, dc, &cap, &promo)) {
              int vcap = value_of_piece_code(cap);
              int deltaS0 = white_to_move ? +vcap : -vcap;
              int score = rootSign * (baseS0 + deltaS0);
              if (!found || score > bestScore) { found = true; bestScore = score; bestCode = encode12(sr, sc, dr, dc); }
            }
          }
        }
        /* Castling options (legal function does all checks) */
        if (sr == (root_white ? 7 : 0) && sc == 4) {
          int dest_k = 6, dest_q = 2;
          uint8_t cap; bool promo;
          if (is_legal_move_and_effects(s, sr, sc, sr, dest_k, &cap, &promo)) {
            int score = rootSign * (baseS0 + 30); /* tiny bonus */
            if (!found || score > bestScore) { found = true; bestScore = score; bestCode = encode12(sr, sc, sr, dest_k); }
          }
          if (is_legal_move_and_effects(s, sr, sc, sr, dest_q, &cap, &promo)) {
            int score = rootSign * (baseS0 + 30);
            if (!found || score > bestScore) { found = true; bestScore = score; bestCode = encode12(sr, sc, sr, dest_q); }
          }
        }
      }
    }
  }

  if (!found) return false;
  *best_code_out = bestCode;
  return true;
}

/* === Terminal status (checkmate/stalemate) === */
static int game_status(const ChessState *s) {
  if (exists_any_legal_move(s)) return GAME_ONGOING;
  bool side_white = s->white_to_move != 0u;
  if (king_in_check(s, side_white)) return GAME_CHECKMATE;
  return GAME_STALEMATE;
}

/* === Driver: play to depth === */
#ifndef MAX_DEPTH
#define MAX_DEPTH 4
#endif

static uint16_t g_played_moves[MAX_DEPTH];
static int      g_num_played = 0;
static int      g_last_status = GAME_ONGOING;

uint16_t const *chessengine_moves_ptr(void) { return g_played_moves; }
int chessengine_moves_len(void) { return g_num_played; }
int chessengine_last_status(void) { return g_last_status; }

void play_to_depth(ChessState *s, int depth) {
  if (depth > MAX_DEPTH) depth = MAX_DEPTH;

  g_num_played = 0;
  bool root_white = s->white_to_move != 0u;

  for (int ply = 0; ply < depth; ++ply) {
    /* Proper mate/stalemate detection before attempting a move */
    g_last_status = game_status(s);
    if (g_last_status != GAME_ONGOING) break;

    bool white_to_move = s->white_to_move != 0u;

    if (white_to_move == root_white) {
      /* Deterministic best move for root side */
      uint16_t code = 0;
      bool ok = choose_best_move_one_ply(s, root_white, &code);
      if (!ok) { /* no legal moves: should have been caught by game_status() */
        g_last_status = game_status(s);
        break;
      }
      int sr, sc, dr, dc; decode12(code, &sr, &sc, &dr, &dc);
      uint8_t cap; bool promo;
      bool legal = is_legal_move_and_effects(s, sr, sc, dr, dc, &cap, &promo);
      if (!legal) { /* belt & suspenders; should not happen */
        g_last_status = game_status(s);
        break;
      }
      apply_move(s, sr, sc, dr, dc);
      g_played_moves[g_num_played++] = code;
    } else {
      /* Opponent: if no legal move -> mate/stalemate; else nondet legal move */
      if (!exists_any_legal_move(s)) {
        g_last_status = game_status(s);
        break;
      }
      uint16_t code = nondet_uint16_t() % 4096u;
      int sr, sc, dr, dc; decode12(code, &sr, &sc, &dr, &dc);
      uint8_t cap; bool promo;
      bool legal = is_legal_move_and_effects(s, sr, sc, dr, dc, &cap, &promo);
      __CPROVER_assume(legal);
      apply_move(s, sr, sc, dr, dc);
      g_played_moves[g_num_played++] = code;
    }
  }

  /* Final status after last move or depth cap */
  if (g_last_status == GAME_ONGOING) g_last_status = game_status(s);
}

#include <stdio.h>
int main(void) {
  play_to_depth(&g_state, MAX_DEPTH);
  printf("Plies played: %d\n", g_num_played);
  for (int i = 0; i < g_num_played; ++i) {
    int sr, sc, dr, dc; decode12(chessengine_moves_ptr()[i], &sr, &sc, &dr, &dc);
    printf("%d: (%d,%d)->(%d,%d)\n", i+1, sr, sc, dr, dc);
  }
  int st = chessengine_last_status();
  if (st == GAME_CHECKMATE) puts("Result: Checkmate");
  else if (st == GAME_STALEMATE) puts("Result: Stalemate");
  else puts("Result: Ongoing");
  return 0;
}
