#include <stdint.h>
#include <assert.h>
#include <stdbool.h>
#include <string.h>

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

typedef struct {
  uint8_t cells_[8][4];
} Chessboard;

Figure FigAt(const Chessboard *b, int8_t r, int8_t c) {
  assert(0 <= r && r < 8);
  assert(0 <= c && c < 8);
  const int8_t f = (b->cells_[r][c / 2] >> (4 * (c % 2))) & 0xF;
  assert(NoFig <= f);
  assert(f < TotFigs);
  return f;
}

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

static inline bool BoardsEqual(const Chessboard *lhs, const Chessboard *rhs) {
  return memcmp(lhs->cells_, rhs->cells_, sizeof(lhs->cells_)) == 0;
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

static bool IsSquareAttacked(const Chessboard *board, int target_row, int target_col, int attacker_color);

static bool KingInCheck(const Chessboard *board, int color) {
  int row = -1;
  int col = -1;
  if (!FindKing(board, color, &row, &col))
    return true;
  return IsSquareAttacked(board, row, col, 1 - color);
}

static void ApplyMove(const Chessboard *from, Chessboard *to, const MoveDesc *mv) {
  *to = *from;
  const Figure mover = FigAt(from, mv->src_row, mv->src_col);
  const Figure placed = (mv->promotion != NoFig) ? mv->promotion : mover;
  SetFig(to, mv->src_row, mv->src_col, NoFig);
  SetFig(to, mv->dst_row, mv->dst_col, placed);
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

static bool AddPawnMoves(const Chessboard *board, int color, int r, int c, MoveDesc *list, int *count, int max_count);
static bool AddKnightMoves(const Chessboard *board, int color, int r, int c, MoveDesc *list, int *count, int max_count);
static bool AddSlidingMoves(const Chessboard *board, int color, int r, int c, const int (*dirs)[2], int dir_count, MoveDesc *list, int *count, int max_count);
static bool AddKingMoves(const Chessboard *board, int color, int r, int c, MoveDesc *list, int *count, int max_count);

static void GenerateLegalMoves(const Chessboard *board, int color, MoveDesc *list, int *count, int max_count) {
  *count = 0;
  for (int r = 0; r < 8; ++r) {
    for (int c = 0; c < 8; ++c) {
      const Figure f = FigAt(board, r, c);
      if (FigColor(f) != color)
        continue;
      const PieceType type = FigPiece(f);
      bool ok = true;
      switch (type) {
        case PiecePawn:
          ok = AddPawnMoves(board, color, r, c, list, count, max_count);
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
          ok = AddKingMoves(board, color, r, c, list, count, max_count);
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

static bool AddPawnMoves(const Chessboard *board, int color, int r, int c, MoveDesc *list, int *count, int max_count) {
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

  if (r == en_passant_row) {
    for (int dc = -1; dc <= 1; dc += 2) {
      const int adjacent_col = c + dc;
      if (!IsInside(r, adjacent_col))
        continue;
      const Figure adjacent = FigAt(board, r, adjacent_col);
      if (adjacent == NoFig || FigPiece(adjacent) != PiecePawn || FigColor(adjacent) == color)
        continue;
      const int target_row = r + forward;
      const int target_col = adjacent_col;
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
    int nr = r + dirs[d][0];
    int nc = c + dirs[d][1];
    while (IsInside(nr, nc)) {
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
      nr += dirs[d][0];
      nc += dirs[d][1];
    }
  }
  return true;
}

static bool AddKingMoves(const Chessboard *board, int color, int r, int c, MoveDesc *list, int *count, int max_count) {
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

  if (KingInCheck(board, color))
    return true;

  const int opponent = 1 - color;
  if (color == ColorWhite && r == 7 && c == 4) {
    if (FigAt(board, 7, 5) == NoFig && FigAt(board, 7, 6) == NoFig &&
        FigAt(board, 7, 7) == WhiteRook &&
        !IsSquareAttacked(board, 7, 5, opponent) &&
        !IsSquareAttacked(board, 7, 6, opponent)) {
      MoveDesc mv = {7, 4, 7, 6, NoFig, false, 7, 5};
      if (!AppendMove(board, color, list, count, max_count, &mv))
        return false;
    }
    if (FigAt(board, 7, 1) == NoFig && FigAt(board, 7, 2) == NoFig &&
        FigAt(board, 7, 3) == NoFig && FigAt(board, 7, 0) == WhiteRook &&
        !IsSquareAttacked(board, 7, 3, opponent) &&
        !IsSquareAttacked(board, 7, 2, opponent)) {
      MoveDesc mv = {7, 4, 7, 2, NoFig, false, 0, 3};
      if (!AppendMove(board, color, list, count, max_count, &mv))
        return false;
    }
  } else if (color == ColorBlack && r == 0 && c == 4) {
    if (FigAt(board, 0, 5) == NoFig && FigAt(board, 0, 6) == NoFig &&
        FigAt(board, 0, 7) == BlackRook &&
        !IsSquareAttacked(board, 0, 5, opponent) &&
        !IsSquareAttacked(board, 0, 6, opponent)) {
      MoveDesc mv = {0, 4, 0, 6, NoFig, false, 7, 5};
      if (!AppendMove(board, color, list, count, max_count, &mv))
        return false;
    }
    if (FigAt(board, 0, 1) == NoFig && FigAt(board, 0, 2) == NoFig &&
        FigAt(board, 0, 3) == NoFig && FigAt(board, 0, 0) == BlackRook &&
        !IsSquareAttacked(board, 0, 3, opponent) &&
        !IsSquareAttacked(board, 0, 2, opponent)) {
      MoveDesc mv = {0, 4, 0, 2, NoFig, false, 0, 3};
      if (!AppendMove(board, color, list, count, max_count, &mv))
        return false;
    }
  }

  return true;
}

static bool IsSquareAttacked(const Chessboard *board, int target_row, int target_col, int attacker_color) {
  assert(IsInside(target_row, target_col));

  const int pawn_row_offset = (attacker_color == ColorWhite) ? 1 : -1;
  for (int dc = -1; dc <= 1; dc += 2) {
    const int r = target_row + pawn_row_offset;
    const int c = target_col + dc;
    if (IsInside(r, c)) {
      const Figure f = FigAt(board, r, c);
      if (f != NoFig && FigColor(f) == attacker_color && FigPiece(f) == PiecePawn)
        return true;
    }
  }

  static const int knight_offsets[8][2] = {
    {-2, -1}, {-2, 1}, {-1, -2}, {-1, 2},
    {1, -2},  {1, 2},  {2, -1},  {2, 1}};
  for (int i = 0; i < 8; ++i) {
    const int r = target_row + knight_offsets[i][0];
    const int c = target_col + knight_offsets[i][1];
    if (!IsInside(r, c))
      continue;
    const Figure f = FigAt(board, r, c);
    if (f != NoFig && FigColor(f) == attacker_color && FigPiece(f) == PieceKnight)
      return true;
  }

  const int rook_dirs[4][2] = {{1, 0}, {-1, 0}, {0, 1}, {0, -1}};
  for (int d = 0; d < 4; ++d) {
    int r = target_row + rook_dirs[d][0];
    int c = target_col + rook_dirs[d][1];
    while (IsInside(r, c)) {
      const Figure f = FigAt(board, r, c);
      if (f == NoFig) {
        r += rook_dirs[d][0];
        c += rook_dirs[d][1];
        continue;
      }
      if (FigColor(f) == attacker_color) {
        const PieceType type = FigPiece(f);
        if (type == PieceRook || type == PieceQueen)
          return true;
      }
      break;
    }
  }

  const int bishop_dirs[4][2] = {{1, 1}, {1, -1}, {-1, 1}, {-1, -1}};
  for (int d = 0; d < 4; ++d) {
    int r = target_row + bishop_dirs[d][0];
    int c = target_col + bishop_dirs[d][1];
    while (IsInside(r, c)) {
      const Figure f = FigAt(board, r, c);
      if (f == NoFig) {
        r += bishop_dirs[d][0];
        c += bishop_dirs[d][1];
        continue;
      }
      if (FigColor(f) == attacker_color) {
        const PieceType type = FigPiece(f);
        if (type == PieceBishop || type == PieceQueen)
          return true;
      }
      break;
    }
  }

  for (int dr = -1; dr <= 1; ++dr) {
    for (int dc = -1; dc <= 1; ++dc) {
      if (dr == 0 && dc == 0)
        continue;
      const int r = target_row + dr;
      const int c = target_col + dc;
      if (!IsInside(r, c))
        continue;
      const Figure f = FigAt(board, r, c);
      if (f != NoFig && FigColor(f) == attacker_color && FigPiece(f) == PieceKing)
        return true;
    }
  }

  return false;
}

MoveCat CategorizeMove(const Chessboard *from, const Chessboard *to) {
  if (BoardsEqual(from, to))
    return InvalidMove;

  if (!FindKing(from, ColorWhite, NULL, NULL) || !FindKing(from, ColorBlack, NULL, NULL))
    return InvalidMove;

  int move_color = ColorNone;
  bool has_moving_source = false;
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
      if (ff != NoFig && FigColor(ff) != ColorNone && ft == NoFig) {
        const int color = FigColor(ff);
        if (move_color == ColorNone)
          move_color = color;
        if (color == move_color)
          has_moving_source = true;
      }
    }
  }

  if (diff_count == 0 || move_color == ColorNone || !has_moving_source)
    return InvalidMove;

  MoveDesc moves[MAX_LEGAL_MOVES];
  int move_count = 0;
  GenerateLegalMoves(from, move_color, moves, &move_count, MAX_LEGAL_MOVES);

  bool matched = false;
  for (int i = 0; i < move_count; ++i) {
    Chessboard candidate;
    ApplyMove(from, &candidate, &moves[i]);
    if (BoardsEqual(&candidate, to)) {
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

  MoveDesc reply_moves[MAX_LEGAL_MOVES];
  int reply_count = 0;
  GenerateLegalMoves(to, opponent, reply_moves, &reply_count, MAX_LEGAL_MOVES);

  if (reply_count == 0) {
    if (KingInCheck(to, opponent))
      return (move_color == ColorWhite) ? WhiteWon : BlackWon;
    return Stalemate;
  }

  return NormalMove;
}
