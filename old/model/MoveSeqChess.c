//
// Created by serge on 10/12/25.
//
#include <stdint.h>
#include <assert.h>

const int8_t cRookDirs[6][2] = { {0, 1}, {0, -1}, {1, 0}, {-1, 0},
  {0, -2}, {0, 3} // 2 types of castling
};
const int8_t cBishopDirs[4][2] = { {1, 1}, {-1, 1}, {1, -1}, {-1, -1} };
const int8_t cKnightDirs[8][2] = {
  {1, 2}, {1, -2}, {-1, 2}, {-1, -2},
  {2, 1}, {2, -1}, {-2, 1}, {-2, -1}
};
const int8_t cKingDirs[8][2] = {
  {0, 1}, {0, -1}, {1, 0}, {-1, 0},
  {1, 1}, {-1, 1}, {1, -1}, {-1, -1}
};
const int8_t cPawnDirs[4][2] = {
  {2, 0}, // when the pawn move 2 rows up from the initial cell
  {1, 0},
  {1, -1}, {1, 1} // when the pawn takes an opponent piece, including en-passe
};

typedef struct
{
  uint16_t srcRow_ : 3;
  uint16_t srcCol_ : 3;
  uint16_t iDir_ : 3; // direction ordinal number
  uint16_t magnitude_ : 3; // bishops, rooks and queens can move several cells in that direction
} Move;

