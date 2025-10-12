#ifndef SIMPLE_GEN_CHESSBOARD_H
#define SIMPLE_GEN_CHESSBOARD_H

#include "ChessEngine.h"

static inline void PutInitial(Chessboard *board) {
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

#endif  // SIMPLE_GEN_CHESSBOARD_H
