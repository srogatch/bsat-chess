//
// Created by serge on 10/12/25.
//
#include <stdint.h>
#include <assert.h>

typedef enum
{
  Knight = 0,
  Bishop = 1,
  Rook = 2,
  Queen = 3,
} FigureTypes;

typedef struct
{
  uint8_t row_ : 3;
  uint8_t col_ : 3;
  uint8_t ft_ : 2; // FigureTypes
} FigurePos;

#define MAX_MOVE_SEQ 256
#define MAX_PLAYER_FIGURES 15
#define MAX_PAWNS 8

typedef struct
{
  FigurePos kingPos_; // ft_ field is ignored
  // First nFigs_ entries below correspond to figures (not pawns or the king)
  // Following nPawns_ positions correspond to pawns with ft_ field ignored
  FigurePos fps_[MAX_PLAYER_FIGURES];
  uint8_t nFigs_ : 4; // 0..15
  uint8_t nPawns_ : 4; // 0..8
} PlayerPieces;

typedef enum
{
  WhitePlayer = 0,
  BlackPlayer = 1,
  NoPlayer = 2,
} PlayerTypes;

typedef struct
{
  PlayerPieces whites_;
  PlayerPieces blacks_;
  uint8_t whoseTurn_ : 1;
} ChessBoard;

typedef struct
{
  uint16_t srcRow_ : 3;
  uint16_t srcCol_ : 3;
  uint16_t dstRow_ : 3;
  uint16_t dstCol_ : 3;
} Move;

#include "GenChessboard.h"

extern unsigned short nondet_ushort();

Move NondetMove()
{
  Move ans;
  uint16_t choice = nondet_ushort();
  __CPROVER_assume(0 <= choice && choice < 8*8*8*8);
  ans.srcRow_ = choice % 8;
  choice /= 8;
  ans.srcCol_ = choice % 8;
  choice /= 8;
  ans.dstRow_ = choice % 8;
  choice /= 8;
  ans.dstCol_ = choice % 8;
  return ans;
}

int main()
{
  ChessBoard board;
  PutInitial(&board);
  // TODO: for each current player's move, determine whether this player's win is forced, and if no move forces a win, force stalemate.
  // TODO: in a sequence of moves, in each turn the current player selects the best move, while the other player moves non-deterministically
  // TODO: limit the horizon of the game to MAX_MOVE_SEQ moves
  return 0;
}