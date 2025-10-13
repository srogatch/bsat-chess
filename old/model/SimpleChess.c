#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#ifndef __CPROVER_assert
#define __CPROVER_assert(expr, msg) do { (void)(msg); assert(expr); } while (0)
#endif
#ifndef __CPROVER_assume
#define __CPROVER_assume(expr) do { bool __cp_assume_cond = (expr); if (!__cp_assume_cond) assert(__cp_assume_cond); } while (0)
#endif

#ifndef SIMPLE_CHESS_EXTERNAL_ENGINE

typedef enum {
  NoFig = 0,
  WhitePawn = 1,
  BlackPawn = 2,
  WhiteKnight = 3,
  BlackKnight = 4,
  WhiteBishop = 5,
  BlackBishop = 6,
  WhiteRook = 7,
  BlackRook = 8,
  WhiteQueen = 9,
  BlackQueen = 10,
  WhiteKing = 11,
  BlackKing = 12,
  TotFigs
} Figure;

typedef enum {
  InvalidMove = 0,
  NormalMove = 1,
  Stalemate = 2,
  WhiteWon = 3,
  BlackWon = 4,
  TotMoveCats
} MoveCat;

typedef enum {
  PiecePawn = 0,
  PieceKnight = 1,
  PieceBishop = 2,
  PieceRook = 3,
  PieceQueen = 4,
  PieceKing = 5,
  PieceNone = 6
} PieceType;

enum {
  ColorWhite = 0,
  ColorBlack = 1,
  ColorNone = 2
};

typedef struct {
  uint8_t cells_[8][4];
} Chessboard;

typedef struct {
  bool available;
  int row;
  int col;
} EnPassantInfo;

typedef struct {
  int src_row;
  int src_col;
  int dst_row;
  int dst_col;
  Figure promotion;
  bool is_en_passant;
  int castle_rook_src_col;
  int castle_rook_dst_col;
} MoveDesc;

#define MAX_LEGAL_MOVES 256

static inline bool IsInside(int r, int c) {
  return (0 <= r && r < 8 && 0 <= c && c < 8);
}

static inline int SquareIndex(int row, int col) {
  return row * 8 + col;
}

static inline Figure FigAt(const Chessboard *b, int8_t r, int8_t c) {
  assert(IsInside(r, c));
  const int8_t f = (b->cells_[r][c / 2] >> (4 * (c % 2))) & 0xF;
  assert(NoFig <= f);
  assert(f < TotFigs);
  return (Figure)f;
}

static inline int FigColor(Figure f) {
  if (f == NoFig)
    return ColorNone;
  return (f & 1) ? ColorWhite : ColorBlack;
}

static inline PieceType FigPiece(Figure f) {
  switch (f) {
    case WhitePawn:
    case BlackPawn:
      return PiecePawn;
    case WhiteKnight:
    case BlackKnight:
      return PieceKnight;
    case WhiteBishop:
    case BlackBishop:
      return PieceBishop;
    case WhiteRook:
    case BlackRook:
      return PieceRook;
    case WhiteQueen:
    case BlackQueen:
      return PieceQueen;
    case WhiteKing:
    case BlackKing:
      return PieceKing;
    default:
      break;
  }
  return PieceNone;
}

static inline Figure MakeFig(int color, PieceType piece) {
  static const Figure map[2][6] = {
    {WhitePawn, WhiteKnight, WhiteBishop, WhiteRook, WhiteQueen, WhiteKing},
    {BlackPawn, BlackKnight, BlackBishop, BlackRook, BlackQueen, BlackKing}};
  assert(color == ColorWhite || color == ColorBlack);
  assert(piece >= PiecePawn && piece <= PieceKing);
  return map[color][piece];
}

static inline void SetFig(Chessboard *b, int8_t r, int8_t c, Figure fig) {
  assert(IsInside(r, c));
  uint8_t *cell = &b->cells_[r][c / 2];
  const uint8_t shift = (uint8_t)(4 * (c % 2));
  const uint8_t mask = (uint8_t)(0xF << shift);
  *cell = (uint8_t)((*cell & (uint8_t)~mask) | (uint8_t)(((uint8_t)fig & 0xF) << shift));
}

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

static bool KingInCheckInternal(const Chessboard *board, int color) {
  int row = -1;
  int col = -1;
  if (!FindKing(board, color, &row, &col))
    return true;
  BoardAnalysis analysis;
  AnalyzeBoard(board, &analysis);
  return AttackMapTest(analysis.attack_map[1 - color], row, col);
}

static void ApplyMoveInternal(const Chessboard *from, Chessboard *to, const MoveDesc *mv) {
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
  ApplyMoveInternal(board, &tmp, mv);
  if (KingInCheckInternal(&tmp, color))
    return true;
  list[*count] = *mv;
  ++(*count);
  return true;
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

static bool AddCastlingMoves(const Chessboard *board, int color, int king_row, int king_col, const BoardAnalysis *analysis, MoveDesc *list, int *count, int max_count) {
  const int opponent = 1 - color;
  const int king_targets[2] = {6, 2};
  const int rook_targets[2] = {5, 3};
  const int directions[2] = {1, -1};
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

static void GenerateLegalMovesInternal(const Chessboard *board, int color, bool allow_en_passant, const EnPassantInfo *ep_info, MoveDesc *list, int *count, int max_count) {
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

static int Chess_GenerateLegalMoves(const Chessboard *board, int color, bool allow_en_passant, const EnPassantInfo *ep_info, MoveDesc *list, int max_count) {
  int count = 0;
  GenerateLegalMovesInternal(board, color, allow_en_passant, ep_info, list, &count, max_count);
  return count;
}

static void Chess_ApplyMove(const Chessboard *from, Chessboard *to, const MoveDesc *mv) {
  ApplyMoveInternal(from, to, mv);
}

static bool Chess_KingInCheck(const Chessboard *board, int color) {
  return KingInCheckInternal(board, color);
}

static void PutInitial(Chessboard *board) {
  for (int r = 0; r < 8; ++r) {
    for (int c = 0; c < 4; ++c) {
      board->cells_[r][c] = 0;
    }
  }
  for (int file = 0; file < 8; ++file) {
    SetFig(board, 6, file, WhitePawn);
    SetFig(board, 1, file, BlackPawn);
  }

  SetFig(board, 7, 0, WhiteRook);
  SetFig(board, 7, 7, WhiteRook);
  SetFig(board, 7, 1, WhiteKnight);
  SetFig(board, 7, 6, WhiteKnight);
  SetFig(board, 7, 2, WhiteBishop);
  SetFig(board, 7, 5, WhiteBishop);
  SetFig(board, 7, 3, WhiteQueen);
  SetFig(board, 7, 4, WhiteKing);

  SetFig(board, 0, 0, BlackRook);
  SetFig(board, 0, 7, BlackRook);
  SetFig(board, 0, 1, BlackKnight);
  SetFig(board, 0, 6, BlackKnight);
  SetFig(board, 0, 2, BlackBishop);
  SetFig(board, 0, 5, BlackBishop);
  SetFig(board, 0, 3, BlackQueen);
  SetFig(board, 0, 4, BlackKing);
}

#else

#include "ChessEngine.h"
#include "GenChessboard.h"

#endif

#define MAX_MOVE_SEQ 256
// Limit recursive exploration to a manageable ply depth while staying within MAX_MOVE_SEQ.
#define MAX_SEARCH_DEPTH 6

typedef enum {
  SimpleOutcomeDraw = 0,
  SimpleOutcomeWhiteWin = 1,
  SimpleOutcomeBlackWin = 2
} SimpleOutcome;

typedef struct {
  Chessboard board;
  int whose_turn;
  EnPassantInfo ep_info;
} GameState;

static inline bool OutcomeIsWinFor(SimpleOutcome outcome, int color) {
  if (outcome == SimpleOutcomeDraw)
    return false;
  if (color == ColorWhite)
    return outcome == SimpleOutcomeWhiteWin;
  return outcome == SimpleOutcomeBlackWin;
}

static inline bool OutcomeIsLossFor(SimpleOutcome outcome, int color) {
  if (outcome == SimpleOutcomeDraw)
    return false;
  if (color == ColorWhite)
    return outcome == SimpleOutcomeBlackWin;
  return outcome == SimpleOutcomeWhiteWin;
}

static inline int OutcomeScore(SimpleOutcome outcome, int color) {
  if (OutcomeIsWinFor(outcome, color))
    return 1;
  if (OutcomeIsLossFor(outcome, color))
    return -1;
  return 0;
}

static inline bool OutcomeBetter(SimpleOutcome lhs, SimpleOutcome rhs, int color) {
  const int lhs_score = OutcomeScore(lhs, color);
  const int rhs_score = OutcomeScore(rhs, color);
  return lhs_score > rhs_score;
}

static EnPassantInfo ComputeNextEnPassant(const Chessboard *board, const MoveDesc *mv) {
  EnPassantInfo info = {false, 0, 0};
  const Figure moved = FigAt(board, mv->src_row, mv->src_col);
  if (FigPiece(moved) == PiecePawn) {
    const int delta = mv->dst_row - mv->src_row;
    if (delta == 2 || delta == -2) {
      info.available = true;
      info.row = (mv->src_row + mv->dst_row) / 2;
      info.col = mv->src_col;
      return info;
    }
  }
  return info;
}

static SimpleOutcome EvaluatePosition(const GameState *state, int depth_left);

#ifndef SIMPLE_CHESS_LIBRARY
static bool FindBestMove(const GameState *state, int depth_left, MoveDesc *best_move, SimpleOutcome *best_outcome) {
  const EnPassantInfo *ep_ptr = state->ep_info.available ? &state->ep_info : NULL;
  MoveDesc moves[MAX_LEGAL_MOVES];
  const int move_count = Chess_GenerateLegalMoves(&state->board,
                                                  state->whose_turn,
                                                  state->ep_info.available,
                                                  ep_ptr,
                                                  moves,
                                                  MAX_LEGAL_MOVES);
  if (move_count <= 0)
    return false;

  bool have_best = false;
  SimpleOutcome best = (state->whose_turn == ColorWhite) ? SimpleOutcomeBlackWin : SimpleOutcomeWhiteWin;
  MoveDesc chosen = moves[0];

  for (int idx = 0; idx < move_count && idx < MAX_LEGAL_MOVES; ++idx) {
    GameState next_state;
    Chess_ApplyMove(&state->board, &next_state.board, &moves[idx]);
    next_state.whose_turn = 1 - state->whose_turn;
    next_state.ep_info = ComputeNextEnPassant(&state->board, &moves[idx]);
    const SimpleOutcome outcome = EvaluatePosition(&next_state, depth_left - 1);

    if (!have_best || OutcomeBetter(outcome, best, state->whose_turn)) {
      best = outcome;
      chosen = moves[idx];
      have_best = true;
      if (OutcomeIsWinFor(outcome, state->whose_turn))
        break;
    }
  }

  if (!have_best)
    return false;
  if (best_move)
    *best_move = chosen;
  if (best_outcome)
    *best_outcome = best;
  return true;
}
#endif

static SimpleOutcome EvaluatePosition(const GameState *state, int depth_left) {
  const EnPassantInfo *ep_ptr = state->ep_info.available ? &state->ep_info : NULL;
  MoveDesc moves[MAX_LEGAL_MOVES];
  const int move_count = Chess_GenerateLegalMoves(&state->board,
                                                  state->whose_turn,
                                                  state->ep_info.available,
                                                  ep_ptr,
                                                  moves,
                                                  MAX_LEGAL_MOVES);

  if (move_count <= 0) {
    if (Chess_KingInCheck(&state->board, state->whose_turn)) {
      return (state->whose_turn == ColorWhite) ? SimpleOutcomeBlackWin : SimpleOutcomeWhiteWin;
    }
    return SimpleOutcomeDraw;
  }

  if (depth_left <= 0)
    return SimpleOutcomeDraw;

  bool has_draw = false;
  const int color = state->whose_turn;

  for (int idx = 0; idx < move_count && idx < MAX_LEGAL_MOVES; ++idx) {
    GameState next_state;
    Chess_ApplyMove(&state->board, &next_state.board, &moves[idx]);
    next_state.whose_turn = 1 - color;
    next_state.ep_info = ComputeNextEnPassant(&state->board, &moves[idx]);

    const SimpleOutcome outcome = EvaluatePosition(&next_state, depth_left - 1);
    if (OutcomeIsWinFor(outcome, color))
      return outcome;
    if (outcome == SimpleOutcomeDraw)
      has_draw = true;
  }

  if (has_draw)
    return SimpleOutcomeDraw;

  return (color == ColorWhite) ? SimpleOutcomeBlackWin : SimpleOutcomeWhiteWin;
}

int SimpleChess_EvaluateOutcome(const Chessboard *board,
                                int color,
                                const EnPassantInfo *ep_info,
                                int depth) {
  GameState state;
  state.board = *board;
  state.whose_turn = color;
  if (ep_info) {
    state.ep_info = *ep_info;
  } else {
    state.ep_info.available = false;
    state.ep_info.row = 0;
    state.ep_info.col = 0;
  }
  if (depth < 0)
    depth = 0;
  if (depth > MAX_SEARCH_DEPTH)
    depth = MAX_SEARCH_DEPTH;
  const SimpleOutcome outcome = EvaluatePosition(&state, depth);
  return (int)outcome;
}

#ifndef SIMPLE_CHESS_LIBRARY

#ifdef __CPROVER__
extern unsigned int nondet_uint(void);
static unsigned int PickOpponentMoveIndex(unsigned int upper) {
  unsigned int value = nondet_uint();
  __CPROVER_assume(value < upper);
  return value;
}
#else
static unsigned int PickOpponentMoveIndex(unsigned int upper) {
  (void)upper;
  return 0U;
}
#endif

int main(void) {
  GameState state;
  PutInitial(&state.board);
  state.whose_turn = ColorWhite;
  state.ep_info.available = false;
  state.ep_info.row = 0;
  state.ep_info.col = 0;

  const int hero_color = state.whose_turn;

  for (int ply = 0; ply < MAX_SEARCH_DEPTH; ++ply) {
    MoveDesc best_move;
    SimpleOutcome best_outcome = SimpleOutcomeDraw;
    const int hero_depth = MAX_SEARCH_DEPTH - ply;
    bool has_move = FindBestMove(&state, hero_depth, &best_move, &best_outcome);
    if (!has_move) {
      const bool in_check = Chess_KingInCheck(&state.board, state.whose_turn);
      __CPROVER_assert(!in_check || state.whose_turn != hero_color, "Hero must not face unavoidable checkmate");
      break;
    }

    __CPROVER_assert(OutcomeIsWinFor(best_outcome, hero_color), "Hero move must preserve a forced win");

    Chessboard after_hero;
    Chess_ApplyMove(&state.board, &after_hero, &best_move);
    EnPassantInfo hero_ep = ComputeNextEnPassant(&state.board, &best_move);
    state.board = after_hero;
    state.ep_info = hero_ep;
    state.whose_turn = 1 - state.whose_turn;

    const EnPassantInfo *op_ep_ptr = state.ep_info.available ? &state.ep_info : NULL;
    MoveDesc opponent_moves[MAX_LEGAL_MOVES];
    const int opponent_count = Chess_GenerateLegalMoves(&state.board,
                                                        state.whose_turn,
                                                        state.ep_info.available,
                                                        op_ep_ptr,
                                                        opponent_moves,
                                                        MAX_LEGAL_MOVES);
    if (opponent_count <= 0) {
      const bool in_check = Chess_KingInCheck(&state.board, state.whose_turn);
      __CPROVER_assert(in_check, "Opponent stalemate encountered");
      break;
    }

    const unsigned int choice = PickOpponentMoveIndex((unsigned int)opponent_count);
    const MoveDesc opponent_move = opponent_moves[choice];
    Chessboard after_opponent;
    Chess_ApplyMove(&state.board, &after_opponent, &opponent_move);
    EnPassantInfo opponent_ep = ComputeNextEnPassant(&state.board, &opponent_move);
    state.board = after_opponent;
    state.ep_info = opponent_ep;
    state.whose_turn = 1 - state.whose_turn;

    int remaining_depth = MAX_SEARCH_DEPTH - ply - 1;
    if (remaining_depth < 0)
      remaining_depth = 0;
    SimpleOutcome continuation = EvaluatePosition(&state, remaining_depth);
    __CPROVER_assert(OutcomeIsWinFor(continuation, hero_color), "Hero must retain forced win after opponent move");
  }

  return 0;
}
#endif
