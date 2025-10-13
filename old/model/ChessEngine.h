#ifndef CHESS_ENGINE_H
#define CHESS_ENGINE_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>

#ifdef __cplusplus
extern "C" {
#endif

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

static inline bool BoardsEqual(const Chessboard *lhs, const Chessboard *rhs) {
  for (int r = 0; r < 8; ++r) {
    for (int c = 0; c < 4; ++c) {
      if (lhs->cells_[r][c] != rhs->cells_[r][c])
        return false;
    }
  }
  return true;
}

void Chess_ApplyMove(const Chessboard *from, Chessboard *to, const MoveDesc *mv);
int Chess_GenerateLegalMoves(const Chessboard *board, int color, bool allow_en_passant, const EnPassantInfo *ep_info, MoveDesc *list, int max_count);
bool Chess_KingInCheck(const Chessboard *board, int color);
bool Chess_FindKing(const Chessboard *board, int color, int *row, int *col);
MoveCat CategorizeMove(const Chessboard *from, const Chessboard *to);
void Chess_FormatMove(const MoveDesc *mv, char *buffer, size_t buffer_size);

#ifdef __cplusplus
}
#endif

#endif  // CHESS_ENGINE_H
