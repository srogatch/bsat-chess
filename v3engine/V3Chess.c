#include <stdint.h>
#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

typedef struct
{
  uint8_t row_ : 3;
  uint8_t col_ : 3;
  uint8_t active_ : 1;
} Position;

Position MakePos(const uint8_t row, const uint8_t col, const bool active)
{
  return Position{.row_ = row, .col_ = col, .active_ = active ? 1 : 0};
}

typedef struct
{
  uint16_t srcRow_ : 3;
  uint16_t srcCol_ : 3;
  uint16_t dstRow_ : 3;
  uint16_t dstCol_ : 3;
} Move;

Move MakeMove(const uint16_t srcRow, const uint16_t srcCol, const uint16_t dstRow, const uint16_t dstCol)
{
  return Move{.srcRow_ = srcRow, .srcCol_ = srcCol, .dstRow_ = dstRow, .dstCol_ = dstCol};
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

bool IsWhitePiece(const ChessPiece piece) {
  return piece > 0 && (piece % 2 == 1);
}

bool IsBlackPiece(const ChessPiece piece) {
  return piece > 0 && (piece % 2 == 0);
}

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
} ChessGameState;

ChessPiece GetPieceAt(const ChessGameState *cgs, const uint8_t row, const uint8_t col) {
  return (cgs->board_[row][col/2] >> (4 * (col%2))) & 0xF;
}
void SetPieceAt(ChessGameState *cgs, const uint8_t row, const uint8_t col, const ChessPiece piece)
{
  cgs->board_[row][col/2] &= (0xF << (4 * (1 - col%2)));
  cgs->board_[row][col/2] |= (piece << (4 * (col % 2)));
}

typedef struct
{
  // Whether the king is under attack
  uint8_t isCheck_ : 1;
  // Whether the king can't hide behind a figure and must retreat (or take an attacker)
  // E.g. a check by a knight, or a double-check
  uint8_t mustRetreat_ : 1;
} CheckState;

CheckState MakeCheckState(const bool isCheck, const bool mustRetreat) {
  CheckState ans{.isCheck_ = isCheck ? 1 : 0, .mustRetreat_ = mustRetreat ? 1 : 0};
  return ans;
}

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

bool IsOnBoad(int8_t row, int8_t col)
{
  return row >= 0 && row < 8 && col >= 0 && col < 8;
}

// Returns check state if a king is placed at the specified row and column, e.g. because it stands there in the game,
// or because it transitions the cell during castling.
CheckState IsAttacked(const ChessGameState *cgs, const uint8_t kingRow, const uint8_t kingCol, const bool whiteKing) {
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
      return MakeCheckState(true, true);
    }
  }

  int8_t nAttackers = 0;
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
      const int8_t oppRookRow = kingRow + k * cBishopDirs[iDir][0];
      const int8_t oppRookCol = kingCol + k * cBishopDirs[iDir][1];
      if (!IsOnBoad(oppRookRow, oppRookCol))
      {
        break;
      }
      const ChessPiece piece = GetPieceAt(cgs, oppRookRow, oppRookCol);
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

  return MakeCheckState(nAttackers > 0, nAttackers >= 2);
}

CheckState GetCheckState(const ChessGameState *cgs, bool whiteKing)
{
  return IsAttacked(cgs, whiteKing ? cgs->whiteKingRow_ : cgs->blackKingRow_,
    whiteKing ? cgs->whiteKingCol_ : cgs->blackKingCol_, whiteKing);
}

extern bool nondet_bool();

// Play the game at |cgs|, as I am a deterministic player if |iamDeterm==true| or otherwise as non-deterministic.
// If the previous move of the opponent was 2-cell pawn move, enPasse stores active_==true and the new coords of that pawn.
// Returns +1 if I win, 0 if the game ends in a draw or stalemate, or -1 if I lose.
int8_t Play(ChessGameState *cgs, bool iamDeterm, const Position enPasse, Move *bestMove)
{
  int8_t bestOutcome = -2; // assume I lose unless found a better move
  // First of all check if we need to hide from a check or retreat
  const bool iamWhite = !cgs->blacksTurn_;
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
    // Check the vicinity of opponent's king
    const int8_t oppKingRow = iamWhite ? cgs->blackKingRow_ : cgs->whiteKingRow_;
    const int8_t oppKingCol = iamWhite ? cgs->blackKingCol_ : cgs->whiteKingCol_;
    if (abs(nextKingRow - oppKingRow) <= 1 && abs(nextKingCol - oppKingCol) <= 1)
    {
      // My king can't move too close to the opponent's king
      continue;
    }
    // Prepare to move, even if taking an opponent's piece, but verify that after that my king is not under a check
    ChessGameState nextCgs = *cgs;
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
    SetPieceAt(&nextCgs, myKingRow, myKingCol, NoPiece);
    SetPieceAt(&nextCgs, nextKingRow, nextKingCol, iamWhite ? WhiteKing : BlackKing);
    const CheckState nextCheck = GetCheckState(&nextCgs, iamWhite);
    // If it's still a check, e.g. the cell is also attacked, or there was an opponent's piece protected by another piece
    if (nextCheck.isCheck_)
    {
      continue;
    }
    // We've found a move for our king!
    Move oppMove;
    if (iamDeterm)
    {
      const int8_t outcome = -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove);
      if (outcome > bestOutcome)
      {
        bestOutcome = outcome;
        *bestMove = MakeMove(myKingRow, myKingCol, nextKingRow, nextKingCol);
        if (bestOutcome >= 1)
        {
          return bestOutcome;
        }
      }
    }
    else
    {
      const bool choose = nondet_bool();
      if (choose)
      {
        *bestMove = MakeMove(myKingRow, myKingCol, nextKingRow, nextKingCol);
        return -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove);
      }
    }
  }
  if (kingCheck.mustRetreat_)
  {
    // No more moves available.
    // TODO: return the best available game outcome
  }
  if (kingCheck.isCheck_)
  {
    // TODO: try to hide behind some piece of mine, or take the offending opponent's piece
  }
  // TODO: if a rook moves, wipe off the possibility of castling with that rook
}
