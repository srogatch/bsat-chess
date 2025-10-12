#include <stdint.h>
#include <assert.h>
#include <stdbool.h>
#include <string.h>
#include <stdio.h>

#include "ChessEngine.h"

#ifndef __CPROVER_assert
#define __CPROVER_assert(expr, msg) do { (void)(expr); (void)(msg); } while (0)
#endif
// Number of one-player turns (semi-rounds)
#define MAX_GAME_SEQ 64

typedef struct {
  uint64_t attack_map[2];
} BoardAnalysis;

static inline void AttackMapSet(uint64_t *map, int row, int col) {
  assert(IsInside(row, col));
  const int idx = SquareIndex(row, col);
  *map |= (uint64_t)1 << idx;
}
static inline bool AttackMapTest(uint64_t map, int row, int col) {
  assert(IsInside(row, col));
  const int idx = SquareIndex(row, col);
  return ((map >> idx) & 1ULL) != 0;
}

static void AnalyzeBoard(const Chessboard *board, BoardAnalysis *analysis);

static bool FindKing(const Chessboard *board, int color, int *row, int *col) {
  const Figure king = (color == ColorWhite) ? WhiteKing : BlackKing;
  for (int r = 0; r < 8; ++r) {
    for (int c = 0; c < 8; ++c) {
      if (FigAt(board, r, c) == king) {
        if (row)
          *row = r;
        if (col)
          *col = c;
        return true;
      }
    }
  }
  return false;
}

static bool KingInCheck(const Chessboard *board, int color) {
  int row = -1;
  int col = -1;
  if (!FindKing(board, color, &row, &col))
    return true;
  BoardAnalysis analysis;
  AnalyzeBoard(board, &analysis);
  return AttackMapTest(analysis.attack_map[1 - color], row, col);
}

static void ApplyMove(const Chessboard *from, Chessboard *to, const MoveDesc *mv) {
  *to = *from;
  const Figure mover = FigAt(from, mv->src_row, mv->src_col);
  const Figure placed = (mv->promotion != NoFig) ? mv->promotion : mover;
  SetFig(to, mv->src_row, mv->src_col, NoFig);
  if (mv->is_en_passant) {
    const int capture_row = mv->src_row;
    const int capture_col = mv->dst_col;
    SetFig(to, capture_row, capture_col, NoFig);
  }
  if (mv->castle_rook_src_col >= 0 && mv->castle_rook_dst_col >= 0) {
    const int rook_row = mv->src_row;
    const Figure rook = FigAt(from, rook_row, mv->castle_rook_src_col);
    SetFig(to, rook_row, mv->castle_rook_src_col, NoFig);
    SetFig(to, rook_row, mv->castle_rook_dst_col, rook);
  }
  SetFig(to, mv->dst_row, mv->dst_col, placed);
}

static bool AppendMove(const Chessboard *board, int color, MoveDesc *list, int *count, int max_count, const MoveDesc *mv) {
  if (*count >= max_count)
    return false;
  Chessboard tmp;
  ApplyMove(board, &tmp, mv);
  if (KingInCheck(&tmp, color))
    return true;
  list[*count] = *mv;
  ++(*count);
  return true;
}

static bool AddPawnMoves(const Chessboard *board, int color, int r, int c, bool allow_en_passant, const EnPassantInfo *ep_info, MoveDesc *list, int *count, int max_count);
static bool AddKnightMoves(const Chessboard *board, int color, int r, int c, MoveDesc *list, int *count, int max_count);
static bool AddSlidingMoves(const Chessboard *board, int color, int r, int c, const int (*dirs)[2], int dir_count, MoveDesc *list, int *count, int max_count);
static bool AddKingMoves(const Chessboard *board, int color, int r, int c, const BoardAnalysis *analysis, MoveDesc *list, int *count, int max_count);
static bool AddCastlingMoves(const Chessboard *board, int color, int king_row, int king_col, const BoardAnalysis *analysis, MoveDesc *list, int *count, int max_count);

static void GenerateLegalMoves(const Chessboard *board, int color, bool allow_en_passant, const EnPassantInfo *ep_info, MoveDesc *list, int *count, int max_count) {
  *count = 0;
  BoardAnalysis analysis;
  AnalyzeBoard(board, &analysis);
  for (int r = 0; r < 8; ++r) {
    for (int c = 0; c < 8; ++c) {
      const Figure f = FigAt(board, r, c);
      if (FigColor(f) != color)
        continue;
      const PieceType type = FigPiece(f);
      bool ok = true;
      switch (type) {
        case PiecePawn:
          ok = AddPawnMoves(board, color, r, c, allow_en_passant, ep_info, list, count, max_count);
          break;
        case PieceKnight:
          ok = AddKnightMoves(board, color, r, c, list, count, max_count);
          break;
        case PieceBishop: {
          static const int dirs[4][2] = {{1, 1}, {1, -1}, {-1, 1}, {-1, -1}};
          ok = AddSlidingMoves(board, color, r, c, dirs, 4, list, count, max_count);
          break;
        }
        case PieceRook: {
          static const int dirs[4][2] = {{1, 0}, {-1, 0}, {0, 1}, {0, -1}};
          ok = AddSlidingMoves(board, color, r, c, dirs, 4, list, count, max_count);
          break;
        }
        case PieceQueen: {
          static const int dirs[8][2] = {
            {1, 0},  {-1, 0}, {0, 1},  {0, -1},
            {1, 1},  {1, -1}, {-1, 1}, {-1, -1}};
          ok = AddSlidingMoves(board, color, r, c, dirs, 8, list, count, max_count);
          break;
        }
        case PieceKing:
          ok = AddKingMoves(board, color, r, c, &analysis, list, count, max_count);
          break;
        case PieceNone:
        default:
          break;
      }
      if (!ok)
        return;
    }
  }
}

static bool AddPromotionVariants(const Chessboard *board, int color, int src_row, int src_col, int dst_row, int dst_col, bool is_en_passant, MoveDesc *list, int *count, int max_count) {
  const PieceType promos[4] = {PieceQueen, PieceRook, PieceBishop, PieceKnight};
  for (int i = 0; i < 4; ++i) {
    MoveDesc mv = {src_row, src_col, dst_row, dst_col, MakeFig(color, promos[i]), is_en_passant, -1, -1};
    if (!AppendMove(board, color, list, count, max_count, &mv))
      return false;
  }
  return true;
}

static bool AddPawnMoves(const Chessboard *board, int color, int r, int c, bool allow_en_passant, const EnPassantInfo *ep_info, MoveDesc *list, int *count, int max_count) {
  const int forward = (color == ColorWhite) ? -1 : 1;
  const int start_row = (color == ColorWhite) ? 6 : 1;
  const int promotion_row = (color == ColorWhite) ? 0 : 7;
  const int en_passant_row = (color == ColorWhite) ? 3 : 4;

  const int one_step_row = r + forward;
  if (IsInside(one_step_row, c) && FigAt(board, one_step_row, c) == NoFig) {
    if (one_step_row == promotion_row) {
      if (!AddPromotionVariants(board, color, r, c, one_step_row, c, false, list, count, max_count))
        return false;
    } else {
      MoveDesc mv = {r, c, one_step_row, c, NoFig, false, -1, -1};
      if (!AppendMove(board, color, list, count, max_count, &mv))
        return false;
    }

    const int two_step_row = r + 2 * forward;
    if (r == start_row && IsInside(two_step_row, c) &&
        FigAt(board, two_step_row, c) == NoFig) {
      MoveDesc mv = {r, c, two_step_row, c, NoFig, false, -1, -1};
      if (!AppendMove(board, color, list, count, max_count, &mv))
        return false;
    }
  }

  for (int dc = -1; dc <= 1; dc += 2) {
    const int target_col = c + dc;
    const int target_row = r + forward;
    if (!IsInside(target_row, target_col))
      continue;
    const Figure target = FigAt(board, target_row, target_col);
    if (target != NoFig && FigColor(target) == 1 - color) {
      if (target_row == promotion_row) {
        if (!AddPromotionVariants(board, color, r, c, target_row, target_col, false, list, count, max_count))
          return false;
      } else {
        MoveDesc mv = {r, c, target_row, target_col, NoFig, false, -1, -1};
        if (!AppendMove(board, color, list, count, max_count, &mv))
          return false;
      }
    }
  }

  if (allow_en_passant && r == en_passant_row) {
    for (int dc = -1; dc <= 1; dc += 2) {
      const int adjacent_col = c + dc;
      if (!IsInside(r, adjacent_col))
        continue;
      const Figure adjacent = FigAt(board, r, adjacent_col);
      if (adjacent == NoFig || FigPiece(adjacent) != PiecePawn || FigColor(adjacent) == color)
        continue;
      const int target_row = r + forward;
      const int target_col = adjacent_col;
      if (ep_info && (!ep_info->available || ep_info->row != target_row || ep_info->col != target_col))
        continue;
      if (!IsInside(target_row, target_col))
        continue;
      if (FigAt(board, target_row, target_col) != NoFig)
        continue;
      MoveDesc mv = {r, c, target_row, target_col, NoFig, true, -1, -1};
      if (!AppendMove(board, color, list, count, max_count, &mv))
        return false;
    }
  }
  return true;
}

static bool AddKnightMoves(const Chessboard *board, int color, int r, int c, MoveDesc *list, int *count, int max_count) {
  static const int offsets[8][2] = {
    {-2, -1}, {-2, 1}, {-1, -2}, {-1, 2},
    {1, -2},  {1, 2},  {2, -1},  {2, 1}};
  for (int i = 0; i < 8; ++i) {
    const int nr = r + offsets[i][0];
    const int nc = c + offsets[i][1];
    if (!IsInside(nr, nc))
      continue;
    const Figure target = FigAt(board, nr, nc);
    if (target != NoFig && FigColor(target) == color)
      continue;
    MoveDesc mv = {r, c, nr, nc, NoFig, false, -1, -1};
    if (!AppendMove(board, color, list, count, max_count, &mv))
      return false;
  }
  return true;
}

static bool AddSlidingMoves(const Chessboard *board, int color, int r, int c, const int (*dirs)[2], int dir_count, MoveDesc *list, int *count, int max_count) {
  for (int d = 0; d < dir_count; ++d) {
    for (int step = 1; step < 8; ++step) {
      const int nr = r + dirs[d][0] * step;
      const int nc = c + dirs[d][1] * step;
      if (!IsInside(nr, nc))
        break;
      const Figure target = FigAt(board, nr, nc);
      if (target != NoFig) {
        if (FigColor(target) != color) {
          MoveDesc mv = {r, c, nr, nc, NoFig, false, -1, -1};
          if (!AppendMove(board, color, list, count, max_count, &mv))
            return false;
        }
        break;
      }
      MoveDesc mv = {r, c, nr, nc, NoFig, false, -1, -1};
      if (!AppendMove(board, color, list, count, max_count, &mv))
        return false;
    }
  }
  return true;
}

static bool AddKingMoves(const Chessboard *board, int color, int r, int c, const BoardAnalysis *analysis, MoveDesc *list, int *count, int max_count) {
  assert(analysis);
  for (int dr = -1; dr <= 1; ++dr) {
    for (int dc = -1; dc <= 1; ++dc) {
      if (dr == 0 && dc == 0)
        continue;
      const int nr = r + dr;
      const int nc = c + dc;
      if (!IsInside(nr, nc))
        continue;
      const Figure target = FigAt(board, nr, nc);
      if (target != NoFig && FigColor(target) == color)
        continue;
      MoveDesc mv = {r, c, nr, nc, NoFig, false, -1, -1};
      if (!AppendMove(board, color, list, count, max_count, &mv))
        return false;
    }
  }

  if (AttackMapTest(analysis->attack_map[1 - color], r, c))
    return true;

  return AddCastlingMoves(board, color, r, c, analysis, list, count, max_count);
}

static void AddSlidingAttacks(const Chessboard *board, int attacker_color, int r, int c, const int (*dirs)[2], int dir_count, uint64_t *map) {
  for (int d = 0; d < dir_count; ++d) {
    for (int step = 1; step < 8; ++step) {
      const int nr = r + dirs[d][0] * step;
      const int nc = c + dirs[d][1] * step;
      if (!IsInside(nr, nc))
        break;
      const Figure target = FigAt(board, nr, nc);
      if (target == NoFig) {
        AttackMapSet(map, nr, nc);
        continue;
      }
      if (FigColor(target) != attacker_color)
        AttackMapSet(map, nr, nc);
      break;
    }
  }
}

static void AnalyzeBoard(const Chessboard *board, BoardAnalysis *analysis) {
  assert(analysis);
  analysis->attack_map[ColorWhite] = 0ULL;
  analysis->attack_map[ColorBlack] = 0ULL;

  for (int r = 0; r < 8; ++r) {
    for (int c = 0; c < 8; ++c) {
      const Figure f = FigAt(board, r, c);
      const int attacker_color = FigColor(f);
      if (attacker_color != ColorWhite && attacker_color != ColorBlack)
        continue;
      uint64_t *map = &analysis->attack_map[attacker_color];
      switch (FigPiece(f)) {
        case PiecePawn: {
          const int forward = (attacker_color == ColorWhite) ? -1 : 1;
          const int nr = r + forward;
          if (IsInside(nr, c - 1))
            AttackMapSet(map, nr, c - 1);
          if (IsInside(nr, c + 1))
            AttackMapSet(map, nr, c + 1);
          break;
        }
        case PieceKnight: {
          static const int offsets[8][2] = {
            {-2, -1}, {-2, 1}, {-1, -2}, {-1, 2},
            {1, -2},  {1, 2},  {2, -1},  {2, 1}};
          for (int i = 0; i < 8; ++i) {
            const int nr = r + offsets[i][0];
            const int nc = c + offsets[i][1];
            if (!IsInside(nr, nc))
              continue;
            AttackMapSet(map, nr, nc);
          }
          break;
        }
        case PieceBishop: {
          static const int dirs[4][2] = {{1, 1}, {1, -1}, {-1, 1}, {-1, -1}};
          AddSlidingAttacks(board, attacker_color, r, c, dirs, 4, map);
          break;
        }
        case PieceRook: {
          static const int dirs[4][2] = {{1, 0}, {-1, 0}, {0, 1}, {0, -1}};
          AddSlidingAttacks(board, attacker_color, r, c, dirs, 4, map);
          break;
        }
        case PieceQueen: {
          static const int dirs[8][2] = {
            {1, 0},  {-1, 0}, {0, 1},  {0, -1},
            {1, 1},  {1, -1}, {-1, 1}, {-1, -1}};
          AddSlidingAttacks(board, attacker_color, r, c, dirs, 8, map);
          break;
        }
        case PieceKing: {
          for (int dr = -1; dr <= 1; ++dr) {
            for (int dc = -1; dc <= 1; ++dc) {
              if (dr == 0 && dc == 0)
                continue;
              const int nr = r + dr;
              const int nc = c + dc;
              if (!IsInside(nr, nc))
                continue;
              AttackMapSet(map, nr, nc);
            }
          }
          break;
        }
        case PieceNone:
        default:
          break;
      }
    }
  }
}

static bool AddCastlingMoves(const Chessboard *board, int color, int king_row, int king_col, const BoardAnalysis *analysis, MoveDesc *list, int *count, int max_count) {
  const int opponent = 1 - color;
  const int king_targets[2] = {6, 2};
  const int rook_targets[2] = {5, 3};
  const int directions[2] = {1, -1};  // kingside, queenside
  assert(analysis);
  const uint64_t board_attacks = analysis->attack_map[opponent];

  for (int side = 0; side < 2; ++side) {
    const int dir = directions[side];
    const int king_target_col = king_targets[side];
    const int rook_target_col = rook_targets[side];

    if (king_target_col < 0 || rook_target_col < 0)
      continue;

    if (!IsInside(king_row, king_target_col) || !IsInside(king_row, rook_target_col))
      continue;

    int rook_col = -1;
    for (int step = 1; step < 8; ++step) {
      const int c = king_col + dir * step;
      if (!IsInside(king_row, c))
        break;
      const Figure piece = FigAt(board, king_row, c);
      if (piece == NoFig)
        continue;
      if (FigColor(piece) == color && FigPiece(piece) == PieceRook)
        rook_col = c;
      break;
    }
    if (rook_col < 0)
      continue;

    bool clear_between = true;
    for (int step = 1; step < 8; ++step) {
      const int cc = king_col + dir * step;
      if (!IsInside(king_row, cc)) {
        clear_between = false;
        break;
      }
      if (cc == rook_col)
        break;
      if (FigAt(board, king_row, cc) != NoFig) {
        clear_between = false;
        break;
      }
    }
    if (!clear_between)
      continue;

    bool king_path_clear = true;
    if (king_target_col != king_col) {
      const int step = (king_target_col > king_col) ? 1 : -1;
      bool reached_target = false;
      for (int iter = 1; iter < 8; ++iter) {
        const int cc = king_col + step * iter;
        if (!IsInside(king_row, cc)) {
          king_path_clear = false;
          break;
        }
        if (cc == rook_col) {
          if (cc == king_target_col) {
            reached_target = true;
            break;
          }
          continue;
        }
        if (FigAt(board, king_row, cc) != NoFig) {
          king_path_clear = false;
          break;
        }
        if (cc == king_target_col) {
          reached_target = true;
          break;
        }
      }
      if (!reached_target)
        king_path_clear = false;
      if (!king_path_clear)
        continue;
    }

    bool rook_path_clear = true;
    if (rook_target_col != rook_col) {
      const int step = (rook_target_col > rook_col) ? 1 : -1;
      bool reached_rook_target = false;
      for (int iter = 1; iter < 8; ++iter) {
        const int cc = rook_col + step * iter;
        if (!IsInside(king_row, cc)) {
          rook_path_clear = false;
          break;
        }
        if (cc == rook_target_col) {
          reached_rook_target = true;
          break;
        }
        if (cc == king_col)
          continue;
        if (FigAt(board, king_row, cc) != NoFig) {
          rook_path_clear = false;
          break;
        }
      }
      if (!reached_rook_target)
        rook_path_clear = false;
      if (!rook_path_clear)
        continue;
    }

    Chessboard tmp = *board;
    SetFig(&tmp, king_row, king_col, NoFig);
    SetFig(&tmp, king_row, rook_col, NoFig);
    BoardAnalysis tmp_analysis;
    AnalyzeBoard(&tmp, &tmp_analysis);
    const uint64_t tmp_attacks = tmp_analysis.attack_map[opponent];

    bool safe_path = true;
    if (king_target_col != king_col) {
      const int step = (king_target_col > king_col) ? 1 : -1;
      bool reached_target = false;
      for (int iter = 1; iter < 8; ++iter) {
        const int cc = king_col + step * iter;
        if (!IsInside(king_row, cc)) {
          safe_path = false;
          break;
        }
        if (cc == rook_col) {
          if (cc == king_target_col) {
            reached_target = true;
            break;
          }
          continue;
        }
        if (AttackMapTest(tmp_attacks, king_row, cc)) {
          safe_path = false;
          break;
        }
        if (cc == king_target_col) {
          reached_target = true;
          break;
        }
      }
      if (!reached_target)
        safe_path = false;
    } else if (AttackMapTest(board_attacks, king_row, king_col)) {
      safe_path = false;
    }
    if (!safe_path)
      continue;

    MoveDesc mv = {king_row, king_col, king_row, king_target_col, NoFig, false, rook_col, rook_target_col};
    if (!AppendMove(board, color, list, count, max_count, &mv))
      return false;
  }

  return true;
}

MoveCat CategorizeMove(const Chessboard *from, const Chessboard *to) {
  if (BoardsEqual(from, to))
    return InvalidMove;

  if (!FindKing(from, ColorWhite, NULL, NULL) || !FindKing(from, ColorBlack, NULL, NULL))
    return InvalidMove;

  int move_color = ColorNone;
  int diff_count = 0;

  for (int r = 0; r < 8; ++r) {
    for (int c = 0; c < 8; ++c) {
      const Figure ff = FigAt(from, r, c);
      const Figure ft = FigAt(to, r, c);
      if (ff == ft)
        continue;
      ++diff_count;
      if (ft != NoFig) {
        const int color = FigColor(ft);
        if (color == ColorNone)
          return InvalidMove;
        if (move_color == ColorNone)
          move_color = color;
        else if (move_color != color)
          return InvalidMove;
      }
    }
  }

  if (diff_count == 0 || move_color == ColorNone)
    return InvalidMove;

  bool has_moving_source = false;
  for (int r = 0; r < 8 && !has_moving_source; ++r) {
    for (int c = 0; c < 8; ++c) {
      const Figure ff = FigAt(from, r, c);
      const Figure ft = FigAt(to, r, c);
      if (ff == ft)
        continue;
      if (ff != NoFig && FigColor(ff) == move_color &&
          (ft == NoFig || FigColor(ft) != move_color || FigPiece(ff) != FigPiece(ft))) {
        has_moving_source = true;
        break;
      }
    }
  }

  if (!has_moving_source) {
    return InvalidMove;
  }

  MoveDesc moves[MAX_LEGAL_MOVES];
  int move_count = 0;
  GenerateLegalMoves(from, move_color, true, NULL, moves, &move_count, MAX_LEGAL_MOVES);

  bool matched = false;
  MoveDesc matched_move;
  for (int i = 0; i < move_count; ++i) {
    Chessboard candidate;
    ApplyMove(from, &candidate, &moves[i]);
    if (BoardsEqual(&candidate, to)) {
      matched_move = moves[i];
      matched = true;
      break;
    }
  }

  if (!matched)
    return InvalidMove;

  if (!FindKing(to, move_color, NULL, NULL))
    return InvalidMove;

  const int opponent = 1 - move_color;
  if (!FindKing(to, opponent, NULL, NULL))
    return (move_color == ColorWhite) ? WhiteWon : BlackWon;

  EnPassantInfo ep_info = {false, 0, 0};
  if (matched) {
    const Figure moved_piece = FigAt(from, matched_move.src_row, matched_move.src_col);
    if (FigPiece(moved_piece) == PiecePawn && (matched_move.dst_row - matched_move.src_row == 2 || matched_move.dst_row - matched_move.src_row == -2)) {
      ep_info.available = true;
      ep_info.row = (matched_move.src_row + matched_move.dst_row) / 2;
      ep_info.col = matched_move.src_col;
    }
  }

  MoveDesc reply_moves[MAX_LEGAL_MOVES];
  int reply_count = 0;
  GenerateLegalMoves(to, opponent, ep_info.available, ep_info.available ? &ep_info : NULL, reply_moves, &reply_count, MAX_LEGAL_MOVES);

  if (reply_count == 0) {
    if (KingInCheck(to, opponent))
      return (move_color == ColorWhite) ? WhiteWon : BlackWon;
    return Stalemate;
  }

  return NormalMove;
}

static char PromotionToChar(Figure fig) {
  switch (FigPiece(fig)) {
    case PieceQueen:
      return 'Q';
    case PieceRook:
      return 'R';
    case PieceBishop:
      return 'B';
    case PieceKnight:
      return 'N';
    default:
      break;
  }
  return '\0';
}

void Chess_FormatMove(const MoveDesc *mv, char *buffer, size_t buffer_size) {
  if (buffer_size == 0)
    return;
  if (mv->castle_rook_src_col >= 0 && mv->castle_rook_dst_col >= 0) {
    const char *castle = (mv->dst_col > mv->src_col) ? "O-O" : "O-O-O";
    snprintf(buffer, buffer_size, "%s", castle);
    return;
  }
  const char src_file = (char)('a' + mv->src_col);
  const char src_rank = (char)('8' - mv->src_row);
  const char dst_file = (char)('a' + mv->dst_col);
  const char dst_rank = (char)('8' - mv->dst_row);
  const char promo = PromotionToChar(mv->promotion);
  if (promo != '\0') {
    snprintf(buffer, buffer_size, "%c%c%c%c=%c", src_file, src_rank, dst_file, dst_rank, promo);
  } else {
    snprintf(buffer, buffer_size, "%c%c%c%c", src_file, src_rank, dst_file, dst_rank);
  }
  if (mv->is_en_passant) {
    const size_t len = strlen(buffer);
    if (len + 5 < buffer_size) {
      snprintf(buffer + len, buffer_size - len, " e.p.");
    }
  }
}

int Chess_GenerateLegalMoves(const Chessboard *board, int color, bool allow_en_passant, const EnPassantInfo *ep_info, MoveDesc *list, int max_count) {
  int count = 0;
  GenerateLegalMoves(board, color, allow_en_passant, ep_info, list, &count, max_count);
  return count;
}

void Chess_ApplyMove(const Chessboard *from, Chessboard *to, const MoveDesc *mv) {
  ApplyMove(from, to, mv);
}

bool Chess_KingInCheck(const Chessboard *board, int color) {
  return KingInCheck(board, color);
}

bool Chess_FindKing(const Chessboard *board, int color, int *row, int *col) {
  return FindKing(board, color, row, col);
}

#ifdef __CPROVER__
extern unsigned char nondet_uchar(void);
#else
static unsigned char nondet_uchar(void) {
  return 0;
}
#endif

int main()
{
  #include "Situation.h"
  MoveDesc moves[MAX_LEGAL_MOVES];
  int move_count = 0;
  GenerateLegalMoves(&board, whoseTurn, false, NULL, moves, &move_count, MAX_LEGAL_MOVES);
  if (move_count == 0)
  {
    // Game Over
    return 0;
  }
  int best_move = -1;
  int my_win = -1; // set it to a loss, so that even a stalemate or uncertainty is better
  for (int i = 0; i < MAX_LEGAL_MOVES; ++i)
  {
    if (i >= move_count)
      break;
    char moveBuffer[32];
    Chess_FormatMove(&moves[i], moveBuffer, sizeof(moveBuffer));
    Chessboard nextBoard = board;
    ApplyMove(&board, &nextBoard, &moves[i]);
    MoveCat mc = CategorizeMove(&board, &nextBoard);
    assert(mc != InvalidMove);
    if (mc != NormalMove)
    {
      if (mc == Stalemate)
      {
        if (my_win < 0)
        {
          my_win = 0;
          best_move = i;
          continue;
        }
      }
      else if ((mc == WhiteWon && whoseTurn == ColorWhite) || (mc == BlackWon && whoseTurn == ColorBlack))
      {
        my_win = 1;
        best_move = i;
#ifdef __CPROVER__
        __CPROVER_assert(0, "WIN IN ONE MOVE - CHECK moveBuffer");
#endif
      }
      continue;
    }
    Chessboard sequenceBoard = nextBoard;
    int sequenceTurn = 1 - whoseTurn;
    bool forced_win = true;
    for (int j=0; j<MAX_GAME_SEQ; j++)
    {
      MoveDesc opponentMoves[MAX_LEGAL_MOVES];
      int opponentCount = 0;
      GenerateLegalMoves(&sequenceBoard, sequenceTurn, false, NULL, opponentMoves, &opponentCount, MAX_LEGAL_MOVES);

      if (opponentCount == 0)
      {
        if (KingInCheck(&sequenceBoard, sequenceTurn) &&
            ((sequenceTurn == ColorWhite && whoseTurn == ColorBlack) ||
             (sequenceTurn == ColorBlack && whoseTurn == ColorWhite)))
        {
          my_win = 1;
          best_move = i;
#ifdef __CPROVER__
          __CPROVER_assert(0, "FORCED WIN - CHECK moveBuffer");
#endif
        }
        else
        {
          forced_win = false;
        }
        break;
      }

      unsigned char choice = nondet_uchar();
      int opponent_index = (int)(choice % opponentCount);
      MoveDesc opponent_move = opponentMoves[opponent_index];

      Chessboard afterOpponent;
      ApplyMove(&sequenceBoard, &afterOpponent, &opponent_move);

      MoveCat opponentOutcome = CategorizeMove(&sequenceBoard, &afterOpponent);
      if ((opponentOutcome == WhiteWon && whoseTurn == ColorBlack) ||
          (opponentOutcome == BlackWon && whoseTurn == ColorWhite) ||
          opponentOutcome == Stalemate)
      {
        forced_win = false;
        break;
      }
      if ((opponentOutcome == WhiteWon && whoseTurn == ColorWhite) ||
          (opponentOutcome == BlackWon && whoseTurn == ColorBlack))
      {
        my_win = 1;
        best_move = i;
#ifdef __CPROVER__
        __CPROVER_assert(0, "FORCED WIN - CHECK moveBuffer");
#endif
        break;
      }

      MoveDesc responseMoves[MAX_LEGAL_MOVES];
      int responseCount = 0;
      GenerateLegalMoves(&afterOpponent, whoseTurn, false, NULL, responseMoves, &responseCount, MAX_LEGAL_MOVES);
      if (responseCount == 0)
      {
        forced_win = false;
        break;
      }

      bool winningReply = false;
      for (int r = 0; r < MAX_LEGAL_MOVES; ++r)
      {
        if (r >= responseCount)
          break;
        Chessboard afterResponse;
        ApplyMove(&afterOpponent, &afterResponse, &responseMoves[r]);
        MoveCat responseOutcome = CategorizeMove(&afterOpponent, &afterResponse);
        if ((responseOutcome == WhiteWon && whoseTurn == ColorWhite) ||
            (responseOutcome == BlackWon && whoseTurn == ColorBlack))
        {
          winningReply = true;
#ifdef __CPROVER__
          __CPROVER_assert(0, "FORCED WIN IN TWO - CHECK moveBuffer");
#endif
          break;
        }
        if ((responseOutcome == WhiteWon && whoseTurn == ColorBlack) ||
            (responseOutcome == BlackWon && whoseTurn == ColorWhite))
        {
          forced_win = false;
          break;
        }
      }

      if (!winningReply || !forced_win)
      {
        forced_win = false;
        break;
      }

      my_win = 1;
      best_move = i;
      break;
    }
  }

  (void)best_move;
  (void)my_win;

  return 0;
}
