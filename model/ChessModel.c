//
// Created by serge on 10/11/25.
//
#include <stdint.h>
#include <assert.h>

typedef enum {
  NoFig=0,
  WhitePawn=1,
  BlackPawn=2,
  WhiteKnight=3,
  BlackKnight=4,
  WhiteBishop=5,
  BlackBishop=6,
  WhiteRook=7,
  BlackRook=8,
  WhiteQueen=9,
  BlackQueen=10,
  WhiteKing=11,
  BlackKing=12,
  TotFigs
} Figure;

typedef struct {
  uint8_t cells_[8][4];
} Chessboard;

Figure FigAt(const Chessboard *b, int8_t r, int8_t c) {
  assert(0 <= r && r < 8);
  assert(0 <= c && c < 8);
  const int8_t f = (b->cells_[r][c/2] >> (4 * (c%2))) & 0xF;
  assert(NoFig <= f);
  assert(f < TotFigs);
  return f;
}

typedef enum
{
  InvalidMove = 0,
  NormalMove = 1,
  Stalemate = 2,
  WhiteWon = 3,
  BlackWon = 4,
  TotMoveCats
} MoveCat;

MoveCat IsValidMove(const Chessboard *from, const Chessboard *to)
{
  
}
