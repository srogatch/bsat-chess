#include <stdint.h>
#include <assert.h>
#include <stdlib.h>

#include "svcomp_shim.h"

#define MAX_SEARCH_DEPTH 4
#define MAX_MOVE_FRONT 256

typedef struct
{
  uint8_t row_ : 3;
  uint8_t col_ : 3;
  uint8_t active_ : 1;
} Position;

Position MakePos(const uint8_t row, const uint8_t col, const _Bool active)
{
  Position ans = {.row_ = row, .col_ = col, .active_ = active ? 1 : 0};
  return ans;
}

typedef struct
{
  uint16_t srcRow_ : 3;
  uint16_t srcCol_ : 3;
  uint16_t dstRow_ : 3;
  uint16_t dstCol_ : 3;
  uint16_t iPromo_ : 2; // promotion index 0..3
} Move;

Move MakeMovePromo(const uint16_t srcRow, const uint16_t srcCol, const uint16_t dstRow, const uint16_t dstCol, const uint16_t iPromo)
{
  Move ans = {.srcRow_ = srcRow, .srcCol_ = srcCol, .dstRow_ = dstRow, .dstCol_ = dstCol, .iPromo_ = iPromo};
  return ans;
}

Move MakeMove(const uint16_t srcRow, const uint16_t srcCol, const uint16_t dstRow, const uint16_t dstCol)
{
  return MakeMovePromo(srcRow, srcCol, dstRow, dstCol, 0);
}

typedef enum
{
  NoPiece = 0,
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
} ChessPiece;

_Bool IsWhitePiece(const ChessPiece piece) {
  return piece > 0 && (piece % 2 == 1);
}

_Bool IsBlackPiece(const ChessPiece piece) {
  return piece > 0 && (piece % 2 == 0);
}

// TODO: set can-castlings to 1 when initializing to the start-game position
typedef struct
{
  uint8_t board_[8][4];
  // Whether whites can do short castling
  uint32_t canWhite00_ : 1;
  // Whether whites can do long castling
  uint32_t canWhite000_ : 1;
  // Whether blacks can do short castling
  uint32_t canBlack00_ : 1;
  // Whether blacks can do long castling
  uint32_t canBlack000_ : 1;
  // Whether it's blacks' turn to move
  uint32_t blacksTurn_ : 1;
  // White king's row
  uint32_t whiteKingRow_ : 3;
  // White king's column
  uint32_t whiteKingCol_ : 3;
  // Black king's row
  uint32_t blackKingRow_ : 3;
  // Black king's column
  uint32_t blackKingCol_ : 3;
  // Whether the last move was a double-forward pawn
  uint32_t isEnpasse_ : 1;
  // If en-passe, the column of the pawn that moved
  uint32_t enPasseCol_ : 3;
} ChessGameState;

ChessPiece GetPieceAt(const ChessGameState *cgs, const uint8_t row, const uint8_t col) {
  return (cgs->board_[row][col/2] >> (4 * (col%2))) & 0xF;
}
void SetPieceAt(ChessGameState *cgs, const uint8_t row, const uint8_t col, const ChessPiece piece, _Bool updateCastlings)
{
  cgs->board_[row][col/2] &= (0xF << (4 * (1 - col%2)));
  cgs->board_[row][col/2] |= (piece << (4 * (col % 2)));
  if (updateCastlings)
  {
    if (row == 0 && col == 0)
    {
      cgs->canWhite000_ = 0;
    }
    else if (row == 0 && col == 7)
    {
      cgs->canWhite00_ = 0;
    }
    else if (row == 7 && col == 0)
    {
      cgs->canBlack000_ = 0;
    }
    else if (row == 7 && col == 7)
    {
      cgs->canBlack00_ = 0;
    }
  }
}

uint8_t SaveCastlings(const ChessGameState* cgs)
{
  const uint8_t ans =
    (cgs->canWhite00_ ? 1 : 0)
  | (cgs->canWhite000_ ? 2 : 0)
  | (cgs->canBlack00_ ? 4 : 0)
  | (cgs->canBlack000_ ? 8 : 0);
  return ans;
}

void RestoreCastlings(ChessGameState *nextCgs, const uint8_t canCastle)
{
  nextCgs->canWhite00_ = (canCastle & 1) ? 1 : 0;
  nextCgs->canWhite000_ = (canCastle & 2) ? 1 : 0;
  nextCgs->canBlack00_ = (canCastle & 4) ? 1 : 0;
  nextCgs->canBlack000_ = (canCastle & 8) ? 1 : 0;
}

typedef struct
{
  // Whether the king is under attack
  uint8_t isCheck_ : 1;
  // Whether the king can't hide behind a figure and must retreat (or take an attacker)
  // E.g. a check by a knight, or a double-check
  uint8_t mustRetreat_ : 1;
} CheckState;

CheckState MakeCheckState(const _Bool isCheck, const _Bool mustRetreat) {
  CheckState ans = {.isCheck_ = isCheck ? 1 : 0, .mustRetreat_ = mustRetreat ? 1 : 0};
  return ans;
}

typedef struct
{
  int32_t r_ : 2; // {-1, 0, 1} game result, 1: I win, 0: draw, -1: I lose.
  int32_t k_ : 30; // number of moves to checkmate, 0..MAX_SEARCH_DEPTH-1 if achievable; MAX_SEARCH_DEPTH for no checkmate
} Valuation;

typedef enum
{
  NoGameEnd = 0,
  Stalemate = 1,
  Checkmate = 2
} GameEnds;

static const int8_t cKnightDirs[8][2] = {
  {2, 1}, {2, -1}, {-2, 1}, {-2, -1},
  {1, 2}, {1, -2}, {-1, 2}, {-1, -2}
};
static const int8_t cRookDirs[4][2] = {
  {0, 1}, {0, -1}, {1, 0}, {-1, 0}
};
static const int8_t cBishopDirs[4][2] = {
  {1, 1}, {1, -1}, {-1, 1}, {-1, -1}
};
static const int8_t cKingDirs[8][2] = {
  {0, 1}, {0, -1}, {1, 1}, {1, -1}, {-1, 1}, {-1, -1}, {1, 0}, {-1, 0}
};
static const int8_t cQueenDirs[8][2] = {
  {0, 1}, {0, -1}, {1, 1}, {1, -1}, {-1, 1}, {-1, -1}, {1, 0}, {-1, 0}
};
static const int8_t cWhitePromos[4] = {WhiteKnight, WhiteBishop, WhiteRook, WhiteQueen};
static const int8_t cBlackPromos[4] = {BlackKnight, BlackBishop, BlackRook, BlackQueen};

_Bool IsOnBoad(int8_t row, int8_t col)
{
  return row >= 0 && row < 8 && col >= 0 && col < 8;
}

// Returns check state if a king is placed at the specified row and column, e.g. because it stands there in the game,
// or because it transitions the cell during castling.
CheckState IsAttacked(const ChessGameState *cgs, const uint8_t kingRow, const uint8_t kingCol, const _Bool whiteKing) {
  int8_t nAttackers = 0;

  // Search for opponent's knight making the check
  for (int8_t i=0; i<8; i++)
  {
    const int8_t oppKnightRow = kingRow + cKnightDirs[i][0];
    const int8_t oppKnightCol = kingCol + cKnightDirs[i][1];
    if (!IsOnBoad(oppKnightRow, oppKnightCol))
    {
      continue;
    }
    const ChessPiece piece = GetPieceAt(cgs, oppKnightRow, oppKnightCol);
    if ( (whiteKing && piece == BlackKnight) || (!whiteKing && piece == WhiteKnight) )
    {
      nAttackers++;
      break;
    }
  }

  // Check attacks by opponent's pawns
  for (int8_t dc=-1; dc<=+1; dc+=2)
  {
    const int8_t oppPawnRow = (whiteKing ? kingRow+1 : kingRow-1);
    const int8_t oppPawnCol = kingCol+dc;
    if (!IsOnBoad(oppPawnRow, oppPawnCol)) {
      continue;
    }
    const ChessPiece piece = GetPieceAt(cgs, oppPawnRow, oppPawnCol);
    if ( (whiteKing && piece == BlackPawn) || (!whiteKing && piece == WhitePawn) )
    {
      nAttackers++;
    }
  }

  // Check attacks by opponent's rooks or queens
  for (int8_t iDir=0; iDir<4; iDir++)
  {
    for (int8_t k=1; k<=7; k++)
    {
      const int8_t oppRookRow = kingRow + k * cRookDirs[iDir][0];
      const int8_t oppRookCol = kingCol + k * cRookDirs[iDir][1];
      if (!IsOnBoad(oppRookRow, oppRookCol))
      {
        break;
      }
      const ChessPiece piece = GetPieceAt(cgs, oppRookRow, oppRookCol);
      if ( (whiteKing && (piece == BlackRook || piece == BlackQueen))
        || (!whiteKing && (piece == WhiteRook || piece == WhiteQueen)) )
      {
        nAttackers++;
      }
      // Any piece serves as an obstacle to further pieces
      if (piece != NoPiece)
      {
        break;
      }
    }
  }

  // Check attacks by opponent's bishops or queens
  for (int8_t iDir=0; iDir<4; iDir++)
  {
    for (int8_t k=1; k<=7; k++)
    {
      const int8_t oppBishopRow = kingRow + k * cBishopDirs[iDir][0];
      const int8_t oppBishopCol = kingCol + k * cBishopDirs[iDir][1];
      if (!IsOnBoad(oppBishopRow, oppBishopCol))
      {
        break;
      }
      const ChessPiece piece = GetPieceAt(cgs, oppBishopRow, oppBishopCol);
      if ( (whiteKing && (piece == BlackBishop || piece == BlackQueen))
        || (!whiteKing && (piece == WhiteBishop || piece == WhiteQueen)) )
      {
        nAttackers++;
      }
      // Any piece serves as an obstacle to further pieces
      if (piece != NoPiece)
      {
        break;
      }
    }
  }

  // Check the vicinity of opponent's king
  const int8_t oppKingRow = whiteKing ? cgs->blackKingRow_ : cgs->whiteKingRow_;
  const int8_t oppKingCol = whiteKing ? cgs->blackKingCol_ : cgs->whiteKingCol_;
  if (abs(kingRow - oppKingRow) <= 1 && abs(kingCol - oppKingCol) <= 1)
  {
    // My king can't move too close to the opponent's king, and can't take pieces protected by opponent's king.
    // I can't either castle when the opponent king is attacking a mid-cell.
    nAttackers++;
  }

  return MakeCheckState(nAttackers > 0, nAttackers >= 2);
}

CheckState GetCheckState(const ChessGameState *cgs, _Bool whiteKing)
{
  return IsAttacked(cgs, whiteKing ? cgs->whiteKingRow_ : cgs->blackKingRow_,
    whiteKing ? cgs->whiteKingCol_ : cgs->blackKingCol_, whiteKing);
}

extern _Bool nondet_bool();


// If the previous move of the opponent was 2-cell pawn move, enPasse stores active_==true and the new coords of that pawn.
// Returns +1 if I win, 0 if the game ends in a draw or stalemate, or -1 if I lose.
GameEnds GetMoves(const ChessGameState *cgs, Move *outMoves, int *nMoves)
{
  *nMoves = 0;
  // First of all check if we need to hide from a check or retreat
  const _Bool iamWhite = !cgs->blacksTurn_;
  const int8_t myKingRow = iamWhite ? cgs->whiteKingRow_ : cgs->blackKingRow_;
  const int8_t myKingCol = iamWhite ? cgs->whiteKingCol_ : cgs->blackKingCol_;
  const CheckState kingCheck = GetCheckState(cgs, iamWhite);
  // First of all consider king moves (takes or retreats), because they also work if kingCheck.mustRetreat_==true
  for (int8_t iDir=0; iDir<8; iDir++)
  {
    const int8_t nextKingRow = myKingRow + cKingDirs[iDir][0];
    const int8_t nextKingCol = myKingCol + cKingDirs[iDir][1];
    if (!IsOnBoad(nextKingRow, nextKingCol))
    {
      continue;
    }
    const ChessPiece piece = GetPieceAt(cgs, nextKingRow, nextKingCol);
    if (piece != NoPiece && iamWhite == IsWhitePiece(piece))
    {
      // My king can't move here because there's another piece of the same color.
      continue;
    }
    // Prepare to move, even if taking an opponent's piece, but verify that after that my king is not under a check
    ChessGameState nextCgs = *cgs;
    nextCgs.isEnpasse_ = 0;
    nextCgs.enPasseCol_ = 0;
    // After moving the king, we lose the possibility of castlings
    if (iamWhite)
    {
      nextCgs.canWhite00_ = 0;
      nextCgs.canWhite000_ = 0;
      nextCgs.whiteKingRow_ = nextKingRow;
      nextCgs.whiteKingCol_ = nextKingCol;
    }
    else
    {
      nextCgs.canBlack00_ = 0;
      nextCgs.canBlack000_ = 0;
      nextCgs.blackKingRow_ = nextKingRow;
      nextCgs.blackKingCol_ = nextKingCol;
    }
    SetPieceAt(&nextCgs, myKingRow, myKingCol, NoPiece, 0);
    SetPieceAt(&nextCgs, nextKingRow, nextKingCol, iamWhite ? WhiteKing : BlackKing, 1);
    const CheckState nextCheck = GetCheckState(&nextCgs, iamWhite);
    // If it's still a check, e.g. the cell is also attacked, or there was an opponent's piece protected by another piece
    if (nextCheck.isCheck_)
    {
      continue;
    }
    // We've found a move for our king!
    nextCgs.blacksTurn_ = !cgs->blacksTurn_;
    outMoves[*nMoves] = MakeMove(myKingRow, myKingCol, nextKingRow, nextKingCol);
    (*nMoves)++;
  }
  if (kingCheck.mustRetreat_)
  {
    if (*nMoves == 0)
    {
      // The king must retreat and there are no moves => checkmate
      return Checkmate;
    }
    return NoGameEnd;
  }
  if (!kingCheck.isCheck_) {
    // Try the castlings
    if (iamWhite) {
      if (cgs->canWhite00_ && GetPieceAt(cgs, 0, 7) == WhiteRook) {
        _Bool clear = 1;
        for (int8_t col=5; col<=6; ++col)
        {
          const ChessPiece piece = GetPieceAt(cgs, 0, col);
          if (piece != NoPiece)
          {
            clear = 0;
            break;
          }
          if (IsAttacked(cgs, 0, col, iamWhite).isCheck_)
          {
            clear = 0;
            break;
          }
        }
        if (clear)
        {
          // ChessGameState nextCgs = *cgs;
          // nextCgs.isEnpasse_ = 0;
          // nextCgs.enPasseCol_ = 0;
          // nextCgs.blacksTurn_ = !cgs->blacksTurn_;
          // nextCgs.canWhite00_ = 0;
          // nextCgs.canWhite000_ = 0;
          // // Remove king from the old position
          // SetPieceAt(&nextCgs, myKingRow, myKingCol, NoPiece, 0);
          // // Remove rook from the old position
          // SetPieceAt(&nextCgs, 0, 7, NoPiece, 0);
          // // Put king to the new position
          // SetPieceAt(&nextCgs, 0, 6, WhiteKing, 0);
          // nextCgs.whiteKingRow_ = 0;
          // nextCgs.whiteKingCol_ = 6;
          // // Put rook to the new position
          // SetPieceAt(&nextCgs, 0, 5, WhiteRook, 0);
          outMoves[*nMoves] = MakeMove(myKingRow, myKingCol, 0, 6);
          (*nMoves)++;
        }
      }
      if (cgs->canWhite000_ && GetPieceAt(cgs, 0, 0) == WhiteRook)
      {
        _Bool clear =1;
        for (int8_t col=1; col<=3; ++col)
        {
          const ChessPiece piece = GetPieceAt(cgs, 0, col);
          if (piece != NoPiece)
          {
            clear = 0;
            break;
          }
          if (col >= 2 && IsAttacked(cgs, 0, col, iamWhite).isCheck_)
          {
            clear = 0;
            break;
          }
        }
        if (clear)
        {
          // ChessGameState nextCgs = *cgs;
          // nextCgs.isEnpasse_ = 0;
          // nextCgs.enPasseCol_ = 0;
          // nextCgs.blacksTurn_ = !cgs->blacksTurn_;
          // nextCgs.canWhite00_ = 0;
          // nextCgs.canWhite000_ = 0;
          // // Remove king from the old position
          // SetPieceAt(&nextCgs, myKingRow, myKingCol, NoPiece, 0);
          // // Remove rook from the old position
          // SetPieceAt(&nextCgs, 0, 0, NoPiece, 0);
          // // Put king to the new position
          // SetPieceAt(&nextCgs, 0, 2, WhiteKing, 0);
          // nextCgs.whiteKingRow_ = 0;
          // nextCgs.whiteKingCol_ = 2;
          // // Put rook to the new position
          // SetPieceAt(&nextCgs, 0, 3, WhiteRook, 0);
          outMoves[*nMoves] = MakeMove(myKingRow, myKingCol, 0, 2);
          (*nMoves)++;
        }
      }
    } else {
      if (cgs->canBlack00_ && GetPieceAt(cgs, 7, 7) == BlackRook) {
        _Bool clear =1;
        for (int8_t col=5; col<=6; ++col)
        {
          const ChessPiece piece = GetPieceAt(cgs, 7, col);
          if (piece != NoPiece)
          {
            clear = 0;
            break;
          }
          if (IsAttacked(cgs, 7, col, iamWhite).isCheck_)
          {
            clear = 0;
            break;
          }
        }
        if (clear)
        {
          // ChessGameState nextCgs = *cgs;
          // nextCgs.isEnpasse_ = 0;
          // nextCgs.enPasseCol_ = 0;
          // nextCgs.blacksTurn_ = !cgs->blacksTurn_;
          // nextCgs.canBlack00_ = 0;
          // nextCgs.canBlack000_ = 0;
          // // Remove king from the old position
          // SetPieceAt(&nextCgs, myKingRow, myKingCol, NoPiece, 0);
          // // Remove rook from the old position
          // SetPieceAt(&nextCgs, 7, 7, NoPiece, 0);
          // // Put king to the new position
          // SetPieceAt(&nextCgs, 7, 6, BlackKing, 0);
          // nextCgs.blackKingRow_ = 7;
          // nextCgs.blackKingCol_ = 6;
          // // Put rook to the new position
          // SetPieceAt(&nextCgs, 7, 5, BlackRook, 0);
          outMoves[*nMoves] = MakeMove(myKingRow, myKingCol, 7, 6);
          (*nMoves)++;
        }
      }
      if (cgs->canBlack000_ && GetPieceAt(cgs, 7, 0) == BlackRook) {
        _Bool clear =1;
        for (int8_t col=1; col<=3; ++col)
        {
          const ChessPiece piece = GetPieceAt(cgs, 7, col);
          if (piece != NoPiece)
          {
            clear = 0;
            break;
          }
          if (col >= 2 && IsAttacked(cgs, 7, col, iamWhite).isCheck_)
          {
            clear = 0;
            break;
          }
        }
        if (clear)
        {
          // ChessGameState nextCgs = *cgs;
          // nextCgs.isEnpasse_ = 0;
          // nextCgs.enPasseCol_ = 0;
          // nextCgs.blacksTurn_ = !cgs->blacksTurn_;
          // nextCgs.canBlack00_ = 0;
          // nextCgs.canBlack000_ = 0;
          // // Remove king from the old position
          // SetPieceAt(&nextCgs, myKingRow, myKingCol, NoPiece, 0);
          // // Remove rook from the old position
          // SetPieceAt(&nextCgs, 7, 0, NoPiece, 0);
          // // Put king to the new position
          // SetPieceAt(&nextCgs, 7, 2, BlackKing, 0);
          // nextCgs.blackKingRow_ = 7;
          // nextCgs.blackKingCol_ = 2;
          // // Put rook to the new position
          // SetPieceAt(&nextCgs, 7, 3, BlackRook, 0);
          outMoves[*nMoves] = MakeMove(myKingRow, myKingCol, 7, 2);
          (*nMoves)++;
        }
      }
    }
  }
  // If my king is at a check, try to hide behind some piece of mine, or take the offending opponent's piece
  // Try to move my figures, verifying that after that move my king is not at a check
  // If a rook moves or is taken, wipe off the possibility of castling with that rook
  Position myPieces[16];
  int8_t nPieces = 0;
  for (int8_t srcRow=0; srcRow<8; ++srcRow)
  {
    for (int8_t srcCol=0; srcCol<8; ++srcCol)
    {
      const ChessPiece piece = GetPieceAt(cgs, srcRow, srcCol);
      if (piece == NoPiece || piece == WhiteKing || piece == BlackKing || IsWhitePiece(piece) != iamWhite)
      {
        // No piece or not my piece in this cell, or a king which we've handled above
        continue;
      }
      myPieces[nPieces].row_ = srcRow;
      myPieces[nPieces].col_ = srcCol;
      nPieces++;
    }
  }
  for (int8_t iPiece=0; iPiece<16; iPiece++) {
    if (iPiece >= nPieces)
    {
      break;
    }
    const int8_t srcRow = myPieces[iPiece].row_;
    const int8_t srcCol = myPieces[iPiece].col_;
    const ChessPiece piece = GetPieceAt(cgs, srcRow, srcCol);
    switch (piece)
    {
    case WhitePawn:
    case BlackPawn:
    {
      if (iamWhite && srcRow == 1 || !iamWhite && srcRow == 6)
      {
        const ChessPiece midPiece = GetPieceAt(cgs, srcRow + (iamWhite ? 1 : -1), srcCol);
        const ChessPiece finPiece = GetPieceAt(cgs, srcRow + (iamWhite ? 2 : -2), srcCol);
        if (midPiece == NoPiece && finPiece == NoPiece)
        {
          // The pawn can move 2 cells front, with en-passe option for the opponent
          const Position dstPos = MakePos(iamWhite ? 3 : 4, srcCol,1);
          ChessGameState nextCgs = *cgs;
          nextCgs.isEnpasse_ = 0;
          nextCgs.enPasseCol_ = 0;
          nextCgs.blacksTurn_ = !cgs->blacksTurn_;
          // Remove the pawn from the previous position
          SetPieceAt(&nextCgs, srcRow, srcCol, NoPiece, 0);
          // Put the pawn to the new position
          SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, piece, 0);
          // Fill out the enpasse structures
          nextCgs.isEnpasse_ = 1;
          nextCgs.enPasseCol_ = srcCol;
          if (!GetCheckState(&nextCgs, iamWhite).isCheck_)
          {
            outMoves[*nMoves] = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
            (*nMoves)++;
          }
        }
      }
      // Don't forget abot the en-passe taking of the opponent's pawn
      if (cgs->isEnpasse_)
      {
        const int8_t enPasseRow = (iamWhite ? 4 : 3);
        const _Bool takeLeft = (cgs->enPasseCol_ == srcCol-1 && srcRow == enPasseRow);
        const _Bool takeRight = (cgs->enPasseCol_ == srcCol+1 && srcRow == enPasseRow);
        if (takeLeft || takeRight)
        {
          ChessGameState nextCgs = *cgs;
          nextCgs.isEnpasse_ = 0;
          nextCgs.enPasseCol_ = 0;
          nextCgs.blacksTurn_ = !cgs->blacksTurn_;
          // Remove my pawn from the previous position
          SetPieceAt(&nextCgs, srcRow, srcCol, NoPiece, 0);
          // Remove opponents pawn that we take en-passe
          SetPieceAt(&nextCgs, enPasseRow, cgs->enPasseCol_, NoPiece, 0);
          // Put my pawn to the new position
          Position dstPos = MakePos(iamWhite ? 5 : 2, srcCol + (takeLeft ? -1 : +1), 0);
          SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, piece, 0);
          Move oppMove;
          if (!GetCheckState(&nextCgs, iamWhite).isCheck_)
          {
            outMoves[*nMoves] = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
            (*nMoves)++;
          }
        }
      }
      // Normal pawn moves front, and takes left and right; with promotions!
      for (int8_t dc=-1; dc<=1; dc++) {
        const int8_t dstRow = iamWhite ? srcRow+1 : srcRow-1;
        const int8_t dstCol = srcCol + dc;
        if (!IsOnBoad(dstRow, dstCol)) {
          continue;
        }
        const Position dstPos = MakePos(dstRow, dstCol, 0);
        const ChessPiece aimPiece = GetPieceAt(cgs, dstPos.row_, dstPos.col_);
        if (aimPiece != NoPiece && IsWhitePiece(aimPiece) == iamWhite)
        {
          // My other piece prevents this my pawn from moving there
          continue;
        }
        if ( (dc == 0 && aimPiece == NoPiece) || (dc != 0 && aimPiece != NoPiece && IsWhitePiece(aimPiece) != iamWhite) ) {
          ChessGameState nextCgs = *cgs;
          nextCgs.isEnpasse_ = 0;
          nextCgs.enPasseCol_ = 0;
          nextCgs.blacksTurn_ = !cgs->blacksTurn_;
          // Remove my pawn from the old position
          SetPieceAt(&nextCgs, srcRow, srcCol, NoPiece, 0);
          // Put my pawn to the new position
          SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, piece, dc != 0);
          // Promoted piece selection doesn't influence when it serves as an obstacle to a check to me
          if (!GetCheckState(&nextCgs, iamWhite).isCheck_)
          {
            if (dstPos.row_ == 0 || dstPos.row_ == 7) {
              // Try all kinds of promotions
              const int8_t *pPromos = (iamWhite ? cWhitePromos : cBlackPromos);
              for (int8_t iPromo=0; iPromo<4; iPromo++)
              {
                const ChessPiece promotion = pPromos[iPromo];
                SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, promotion,1);
                outMoves[*nMoves] = MakeMovePromo(srcRow, srcCol, dstPos.row_, dstPos.col_, iPromo);
                (*nMoves)++;
              }
            }
            else
            {
              outMoves[*nMoves] = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
              (*nMoves)++;
            }
          }
        }
      }
      break;
    }
    case WhiteKnight:
    case BlackKnight:
    {
      ChessGameState nextCgs = *cgs;
      nextCgs.isEnpasse_ = 0;
      nextCgs.enPasseCol_ = 0;
      nextCgs.blacksTurn_ = !cgs->blacksTurn_;
      // Remove this knight from the old position
      SetPieceAt(&nextCgs, srcRow, srcCol, NoPiece, 0);
      const uint8_t canCastle = SaveCastlings(&nextCgs);
      for (int8_t iDir=0; iDir<8; iDir++)
      {
        const int8_t dstRow = srcRow + cKnightDirs[iDir][0];
        const int8_t dstCol = srcCol + cKnightDirs[iDir][1];
        if (!IsOnBoad(dstRow, dstCol)) {
          continue;
        }
        const Position dstPos = MakePos(dstRow, dstCol, 0);
        const ChessPiece aimPiece = GetPieceAt(cgs, dstPos.row_, dstPos.col_);
        if (aimPiece != NoPiece && IsWhitePiece(aimPiece) == iamWhite)
        {
          // My another piece prevents from moving there
          continue;
        }
        SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, piece,1);
        if (!GetCheckState(&nextCgs, iamWhite).isCheck_)
        {
          outMoves[*nMoves] = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
          (*nMoves)++;
        }
        // epilogue - restore the aim piece that was there
        SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, aimPiece, 0);
        RestoreCastlings(&nextCgs, canCastle);
      }
      break;
    }
    case WhiteBishop:
    case BlackBishop:
    {
      ChessGameState nextCgs = *cgs;
      nextCgs.isEnpasse_ = 0;
      nextCgs.enPasseCol_ = 0;
      nextCgs.blacksTurn_ = !cgs->blacksTurn_;
      // Remove this bishop from the old position
      SetPieceAt(&nextCgs, srcRow, srcCol, NoPiece, 0);
      const uint8_t canCastle = SaveCastlings(&nextCgs);
      for (int8_t iDir=0; iDir<4; iDir++)
      {
        for (int8_t dist=1; dist<=7; dist++)
        {
          const int8_t dstRow = srcRow + dist * cBishopDirs[iDir][0];
          const int8_t dstCol = srcCol + dist * cBishopDirs[iDir][1];
          if (!IsOnBoad(dstRow, dstCol)) {
            break;
          }
          const Position dstPos = MakePos(dstRow, dstCol, 0);
          const ChessPiece aimPiece = GetPieceAt(&nextCgs, dstPos.row_, dstPos.col_);
          if (aimPiece != NoPiece && IsWhitePiece(aimPiece) == iamWhite)
          {
            // My other piece is an obstacle to further moving in this direction
            break;
          }
          SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, piece,1);
          if (!GetCheckState(&nextCgs, iamWhite).isCheck_)
          {
            outMoves[*nMoves] = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
            (*nMoves)++;
          }
          // epilogue - restore the aim piece that was there
          SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, aimPiece, 0);
          RestoreCastlings(&nextCgs, canCastle);
          if (aimPiece != NoPiece)
          {
            break;
          }
        }
      }
      break;
    }
    case WhiteRook:
    case BlackRook:
    {
      ChessGameState nextCgs = *cgs;
      nextCgs.isEnpasse_ = 0;
      nextCgs.enPasseCol_ = 0;
      nextCgs.blacksTurn_ = !cgs->blacksTurn_;
      // Remove this rook from the old position, forbid castling with this rook.
      SetPieceAt(&nextCgs, srcRow, srcCol, NoPiece,1);
      uint8_t canCastle = SaveCastlings(&nextCgs);
      for (int8_t iDir=0; iDir<4; iDir++)
      {
        for (int8_t dist=1; dist<=7; dist++)
        {
          const int8_t dstRow = srcRow + dist * cRookDirs[iDir][0];
          const int8_t dstCol = srcCol + dist * cRookDirs[iDir][1];
          if (!IsOnBoad(dstRow, dstCol)) {
            break;
          }
          const Position dstPos = MakePos(dstRow, dstCol, 0);
          const ChessPiece aimPiece = GetPieceAt(&nextCgs, dstPos.row_, dstPos.col_);
          if (aimPiece != NoPiece && IsWhitePiece(aimPiece) == iamWhite)
          {
            // My other piece is an obstacle to further moving in this direction
            break;
          }
          SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, piece,1);
          if (!GetCheckState(&nextCgs, iamWhite).isCheck_)
          {
            outMoves[*nMoves] = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
            (*nMoves)++;
          }
          // epilogue - restore the aim piece that was there
          SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, aimPiece, 0);
          RestoreCastlings(&nextCgs, canCastle);
          if (aimPiece != NoPiece)
          {
            break;
          }
        }
      }
      break;
    }
    case WhiteQueen:
    case BlackQueen:
    {
      ChessGameState nextCgs = *cgs;
      nextCgs.isEnpasse_ = 0;
      nextCgs.enPasseCol_ = 0;
      nextCgs.blacksTurn_ = !cgs->blacksTurn_;
      // Remove this queen from the old position
      SetPieceAt(&nextCgs, srcRow, srcCol, NoPiece, 0);
      const uint8_t canCastle = SaveCastlings(&nextCgs);
      for (int8_t iDir=0; iDir<8; iDir++)
      {
        for (int8_t dist=1; dist<=7; dist++)
        {
          const int8_t dstRow = srcRow + dist * cQueenDirs[iDir][0];
          const int8_t dstCol = srcCol + dist * cQueenDirs[iDir][1];
          if (!IsOnBoad(dstRow, dstCol)) {
            break;
          }
          const Position dstPos = MakePos(dstRow, dstCol, 0);
          const ChessPiece aimPiece = GetPieceAt(&nextCgs, dstPos.row_, dstPos.col_);
          if (aimPiece != NoPiece && IsWhitePiece(aimPiece) == iamWhite)
          {
            // My other piece is an obstacle to further moving in this direction
            break;
          }
          SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, piece,1);
          if (!GetCheckState(&nextCgs, iamWhite).isCheck_)
          {
            outMoves[*nMoves] = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
            (*nMoves)++;
          }
          // epilogue - restore the aim piece that was there
          SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, aimPiece, 0);
          RestoreCastlings(&nextCgs, canCastle);
          if (aimPiece != NoPiece)
          {
            break;
          }
        }
      }
      break;
    }
    default:
      assert(0);
    }
  }
  if (*nMoves == 0)
  {
    if (kingCheck.isCheck_)
    {
      // A check and no moves => mate (I lost)
      return Checkmate;
    }
    else
    {
      // No check and no moves => stalemate
      return Stalemate;
    }
  }
  else
  {
    return NoGameEnd;
  }
}

void ApplyMove(ChessGameState *cgs, const Move move)
{
  const ChessPiece srcPiece = GetPieceAt(cgs, move.srcRow_, move.srcCol_);
  const _Bool iamWhite = !cgs->blacksTurn_;
  // TODO: remove asserts to simplify CBMC after the program is debugged
  assert(srcPiece != NoPiece);
  assert(IsWhitePiece(srcPiece) == iamWhite);
  SetPieceAt(cgs, move.srcRow_, move.srcCol_, NoPiece,1);
  cgs->blacksTurn_ = !cgs->blacksTurn_;
  // En-passe capture
  if (cgs->isEnpasse_ && (srcPiece == WhitePawn || srcPiece == BlackPawn) && abs(move.dstCol_ - move.srcCol_) == 1
    && move.dstCol_ == cgs->enPasseCol_)
  {
    const ChessPiece dstPiece = GetPieceAt(cgs, move.dstRow_, move.dstCol_);
    if (dstPiece == NoPiece)
    {
      // TODO: assert there was an opponent's pawn
      SetPieceAt(cgs, move.srcRow_, move.dstCol_, NoPiece, 0);
      SetPieceAt(cgs, move.dstRow_, move.dstCol_, srcPiece, 0);
      cgs->isEnpasse_ = 0;
      cgs->enPasseCol_ = 0;
      return;
    }
  }
  // Double-forward pawn move
  if ( (srcPiece == WhitePawn || srcPiece == BlackPawn) && abs(move.srcRow_ - move.dstRow_) == 2 )
  {
    SetPieceAt(cgs, move.dstRow_, move.dstCol_, srcPiece, 0);
    cgs->isEnpasse_ = 1;
    cgs->enPasseCol_ = move.srcCol_;
    return;
  }
  cgs->isEnpasse_ = 0;
  cgs->enPasseCol_ = 0;
  // Promotions
  if ( (srcPiece == WhitePawn && move.dstRow_ == 7) || (srcPiece == BlackPawn && move.dstRow_ == 0) )
  {
    switch (move.iPromo_)
    {
    case 0:
      SetPieceAt(cgs, move.dstRow_, move.dstCol_, iamWhite ? WhiteKnight : BlackKnight,1);
      break;
    case 1:
      SetPieceAt(cgs, move.dstRow_, move.dstCol_, iamWhite ? WhiteBishop : BlackBishop,1);
      break;
    case 2:
      SetPieceAt(cgs, move.dstRow_, move.dstCol_, iamWhite ? WhiteRook : BlackRook,1);
      break;
    case 3:
      SetPieceAt(cgs, move.dstRow_, move.dstCol_, iamWhite ? WhiteQueen : BlackQueen,1);
      break;
    }
    return;
  }
  // King moves (update cgs cache and lose all castlings), including castlings
  if (srcPiece == WhiteKing || srcPiece == BlackKing)
  {
    // Castling
    if (abs(move.srcCol_ - move.dstCol_) == 2)
    {
      if (move.dstCol_ < move.srcCol_)
      {
        // Long castling 0-0-0
        SetPieceAt(cgs, move.srcRow_, 0, NoPiece, 0);
        SetPieceAt(cgs, move.srcRow_, move.srcCol_-1, iamWhite ? WhiteRook : BlackRook, 0);
      }
      else
      {
        // Short castling 0-0
        SetPieceAt(cgs, move.srcRow_, 7, NoPiece, 0);
        SetPieceAt(cgs, move.srcRow_, move.srcCol_+1, iamWhite ? WhiteRook : BlackRook, 0);
      }
    }
    SetPieceAt(cgs, move.dstRow_, move.dstCol_, srcPiece, 0);
    if (iamWhite)
    {
      cgs->whiteKingRow_ = move.dstRow_;
      cgs->whiteKingCol_ = move.dstCol_;
      cgs->canWhite00_ = 0;
      cgs->canWhite000_ = 0;
    }
    else
    {
      cgs->blackKingRow_ = move.dstRow_;
      cgs->blackKingCol_ = move.dstCol_;
      cgs->canBlack00_ = 0;
      cgs->canBlack000_ = 0;
    }
    return;
  }
  // Else, simply put the piece to the destination cell
  SetPieceAt(cgs, move.dstRow_, move.dstCol_, srcPiece,1);
}

#include "V3SitEval.h"

extern int nondet_int();

int main() {
  ChessGameState cgs;
  InitSituation(&cgs);

  // TODO: adjust array field sensitivity in CBMC to a value more than MAX_MOVE_FRONT
  Move moveOpts[MAX_MOVE_FRONT];
  const int movesToWin = (nondet_int() % MAX_SEARCH_DEPTH) * 2 + 1;

  // TODO: set CBMC unwind to at least 2*MAX_SEARCH_DEPTH+1
  for (int i=0; i<=2*MAX_SEARCH_DEPTH; i++)
  {
    if (i > movesToWin)
    {
      break;
    }
    int nMoves;
    const GameEnds ge = GetMoves(&cgs, moveOpts, &nMoves);
    if (nMoves == 0)
    {
      if (i != movesToWin)
      {
        // Not a solution
        break;
      }
      __CPROVER_assert(ge != Checkmate, "Opponent got a checkmate");
    }
    const int selMove = nondet_int() %  nMoves;
    ApplyMove(&cgs, moveOpts[selMove]);
  }
  return 0;
}
