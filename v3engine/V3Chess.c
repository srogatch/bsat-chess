#include <stdint.h>
#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

#define MAX_SEARCH_DEPTH 64

typedef struct
{
  uint8_t row_ : 3;
  uint8_t col_ : 3;
  uint8_t active_ : 1;
} Position;

Position MakePos(const uint8_t row, const uint8_t col, const bool active)
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

bool IsWhitePiece(const ChessPiece piece) {
  return piece > 0 && (piece % 2 == 1);
}

bool IsBlackPiece(const ChessPiece piece) {
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
  CheckState ans = {.isCheck_ = isCheck ? 1 : 0, .mustRetreat_ = mustRetreat ? 1 : 0};
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
static const int8_t cQueenDirs[8][2] = {
  {0, 1}, {0, -1}, {1, 1}, {1, -1}, {-1, 1}, {-1, -1}, {1, 0}, {-1, 0}
};
static const int8_t cWhitePromos[4] = {WhiteKnight, WhiteBishop, WhiteRook, WhiteQueen};
static const int8_t cBlackPromos[4] = {BlackKnight, BlackBishop, BlackRook, BlackQueen};

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
int8_t Play(const ChessGameState *cgs, bool iamDeterm, const Position enPasse, Move *bestMove, const int depth)
{
  // TODO: instead, check whether we are in a terminal state where no player is able to win
  if (depth >= MAX_SEARCH_DEPTH)
  {
    return 0; // Draw
  }
  bool nondetHadMove = false;
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
    nextCgs.blacksTurn_ = !cgs->blacksTurn_;
    Move oppMove;
    if (iamDeterm)
    {
      const int8_t outcome = -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
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
      *bestMove = MakeMove(myKingRow, myKingCol, nextKingRow, nextKingCol);
      nondetHadMove = true;
      if (choose)
      {
        return -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
      }
    }
  }
  if (kingCheck.mustRetreat_)
  {
    // No more moves available. Return the best available game outcome.
    return bestOutcome;
  }
  if (!kingCheck.isCheck_) {
    // Try the castlings
    if (iamWhite) {
      if (cgs->canWhite00_) {
        bool clear = true;
        for (int8_t col=5; col<=6; ++col)
        {
          const ChessPiece piece = GetPieceAt(cgs, 0, col);
          if (piece != NoPiece)
          {
            clear = false;
            break;
          }
          if (IsAttacked(cgs, 0, col, iamWhite).isCheck_)
          {
            clear = false;
            break;
          }
        }
        if (clear)
        {
          ChessGameState nextCgs = *cgs;
          nextCgs.blacksTurn_ = !cgs->blacksTurn_;
          nextCgs.canWhite00_ = 0;
          nextCgs.canWhite000_ = 0;
          // Remove king from the old position
          SetPieceAt(&nextCgs, myKingRow, myKingCol, NoPiece);
          // Remove rook from the old position
          SetPieceAt(&nextCgs, 0, 7, NoPiece);
          // Put king to the new position
          SetPieceAt(&nextCgs, 0, 6, WhiteKing);
          nextCgs.whiteKingRow_ = 0;
          nextCgs.whiteKingCol_ = 6;
          // Put rook to the new position
          SetPieceAt(&nextCgs, 0, 5, WhiteRook);
          Move oppMove;
          if (iamDeterm)
          {
            const int8_t outcome = -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
            if (outcome > bestOutcome)
            {
              bestOutcome = outcome;
              *bestMove = MakeMove(myKingRow, myKingCol, 0, 6);
              if (bestOutcome >= 1)
              {
                return bestOutcome;
              }
            }
          }
          else
          {
            const bool choose = nondet_bool();
            *bestMove = MakeMove(myKingRow, myKingCol, 0, 6);
            nondetHadMove = true;
            if (choose)
            {
              return -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
            }
          }
        }
      }
      if (cgs->canWhite000_)
      {
        bool clear = true;
        for (int8_t col=1; col<=3; ++col)
        {
          const ChessPiece piece = GetPieceAt(cgs, 0, col);
          if (piece != NoPiece)
          {
            clear = false;
            break;
          }
          if (IsAttacked(cgs, 0, col, iamWhite).isCheck_)
          {
            clear = false;
            break;
          }
        }
        if (clear)
        {
          ChessGameState nextCgs = *cgs;
          nextCgs.blacksTurn_ = !cgs->blacksTurn_;
          nextCgs.canWhite00_ = 0;
          nextCgs.canWhite000_ = 0;
          // Remove king from the old position
          SetPieceAt(&nextCgs, myKingRow, myKingCol, NoPiece);
          // Remove rook from the old position
          SetPieceAt(&nextCgs, 0, 0, NoPiece);
          // Put king to the new position
          SetPieceAt(&nextCgs, 0, 2, WhiteKing);
          nextCgs.whiteKingRow_ = 0;
          nextCgs.whiteKingCol_ = 2;
          // Put rook to the new position
          SetPieceAt(&nextCgs, 0, 3, WhiteRook);
          Move oppMove;
          if (iamDeterm)
          {
            const int8_t outcome = -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
            if (outcome > bestOutcome)
            {
              bestOutcome = outcome;
              *bestMove = MakeMove(myKingRow, myKingCol, 0, 2);
              if (bestOutcome >= 1)
              {
                return bestOutcome;
              }
            }
          }
          else
          {
            const bool choose = nondet_bool();
            *bestMove = MakeMove(myKingRow, myKingCol, 0, 2);
            nondetHadMove = true;
            if (choose)
            {
              return -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
            }
          }
        }
      }
    } else {
      if (cgs->canBlack00_) {
        bool clear = true;
        for (int8_t col=5; col<=6; ++col)
        {
          const ChessPiece piece = GetPieceAt(cgs, 7, col);
          if (piece != NoPiece)
          {
            clear = false;
            break;
          }
          if (IsAttacked(cgs, 7, col, iamWhite).isCheck_)
          {
            clear = false;
            break;
          }
        }
        if (clear)
        {
          ChessGameState nextCgs = *cgs;
          nextCgs.blacksTurn_ = !cgs->blacksTurn_;
          nextCgs.canBlack00_ = 0;
          nextCgs.canBlack000_ = 0;
          // Remove king from the old position
          SetPieceAt(&nextCgs, myKingRow, myKingCol, NoPiece);
          // Remove rook from the old position
          SetPieceAt(&nextCgs, 7, 7, NoPiece);
          // Put king to the new position
          SetPieceAt(&nextCgs, 7, 6, BlackKing);
          nextCgs.blackKingRow_ = 7;
          nextCgs.blackKingCol_ = 6;
          // Put rook to the new position
          SetPieceAt(&nextCgs, 7, 5, BlackRook);
          Move oppMove;
          if (iamDeterm)
          {
            const int8_t outcome = -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
            if (outcome > bestOutcome)
            {
              bestOutcome = outcome;
              *bestMove = MakeMove(myKingRow, myKingCol, 7, 6);
              if (bestOutcome >= 1)
              {
                return bestOutcome;
              }
            }
          }
          else
          {
            const bool choose = nondet_bool();
            *bestMove = MakeMove(myKingRow, myKingCol, 7, 6);
            nondetHadMove = true;
            if (choose)
            {
              return -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
            }
          }
        }
      }
      if (cgs->canBlack000_) {
        bool clear = true;
        for (int8_t col=1; col<=3; ++col)
        {
          const ChessPiece piece = GetPieceAt(cgs, 7, col);
          if (piece != NoPiece)
          {
            clear = false;
            break;
          }
          if (IsAttacked(cgs, 7, col, iamWhite).isCheck_)
          {
            clear = false;
            break;
          }
        }
        if (clear)
        {
          ChessGameState nextCgs = *cgs;
          nextCgs.blacksTurn_ = !cgs->blacksTurn_;
          nextCgs.canBlack00_ = 0;
          nextCgs.canBlack000_ = 0;
          // Remove king from the old position
          SetPieceAt(&nextCgs, myKingRow, myKingCol, NoPiece);
          // Remove rook from the old position
          SetPieceAt(&nextCgs, 7, 0, NoPiece);
          // Put king to the new position
          SetPieceAt(&nextCgs, 7, 2, BlackKing);
          nextCgs.blackKingRow_ = 7;
          nextCgs.blackKingCol_ = 2;
          // Put rook to the new position
          SetPieceAt(&nextCgs, 7, 3, BlackRook);
          Move oppMove;
          if (iamDeterm)
          {
            const int8_t outcome = -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
            if (outcome > bestOutcome)
            {
              bestOutcome = outcome;
              *bestMove = MakeMove(myKingRow, myKingCol, 7, 2);
              if (bestOutcome >= 1)
              {
                return bestOutcome;
              }
            }
          }
          else
          {
            const bool choose = nondet_bool();
            *bestMove = MakeMove(myKingRow, myKingCol, 7, 2);
            nondetHadMove = true;
            if (choose)
            {
              return -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
            }
          }
        }
      }
    }
  }
  // TODO: if my king is at a check, try to hide behind some piece of mine, or take the offending opponent's piece
  // TODO: try to move my figures, verifying that after that move my king is not at a check
  // TODO: if a rook moves, wipe off the possibility of castling with that rook
  for (int8_t srcRow=0; srcRow<8; ++srcRow)
  {
    for (int8_t srcCol=0; srcCol<8; ++srcCol)
    {
      const ChessPiece piece = GetPieceAt(cgs, srcRow, srcCol);
      if (piece == NoPiece || IsWhitePiece(piece) != iamWhite)
      {
        // No piece or not my piece in this cell
        continue;
      }
      switch (piece)
      {
      case WhitePawn:
      case BlackPawn:
      {
        if (iamWhite && srcRow == 1 || !iamWhite && srcRow == 6)
        {
          const ChessPiece midPiece = GetPieceAt(cgs, srcRow + (iamWhite ? 1 : -1), srcCol);
          if (midPiece == NoPiece)
          {
            // The pawn can move 2 cells front, with en-passe option for the opponent
            const Position dstPos = MakePos(iamWhite ? 3 : 4, srcCol, true);
            ChessGameState nextCgs = *cgs;
            nextCgs.blacksTurn_ = !cgs->blacksTurn_;
            // Remove the pawn from the previous position
            SetPieceAt(&nextCgs, srcRow, srcCol, NoPiece);
            // Put the pawn to the new position
            SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, piece);
            if (!GetCheckState(&nextCgs, iamWhite).isCheck_)
            {
              Move oppMove;
              if (iamDeterm)
              {
                const int8_t outcome = -Play(&nextCgs, !iamDeterm, dstPos, &oppMove, depth + 1);
                if (outcome > bestOutcome)
                {
                  bestOutcome = outcome;
                  *bestMove = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
                  if (bestOutcome >= 1)
                  {
                    return bestOutcome;
                  }
                }
              }
              else
              {
                const bool choose = nondet_bool();
                *bestMove = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
                nondetHadMove = true;
                if (choose)
                {
                  return -Play(&nextCgs, !iamDeterm, dstPos, &oppMove, depth + 1);
                }
              }
            }
          }
        }
        // Don't forget abot the en-passe taking of the opponent's pawn
        if (enPasse.active_)
        {
          const bool takeLeft = (enPasse.col_ == srcCol-1 && enPasse.row_ == srcRow);
          const bool takeRight = (enPasse.col_ == srcCol+1 && enPasse.row_ == srcRow);
          if (takeLeft || takeRight)
          {
            ChessGameState nextCgs = *cgs;
            nextCgs.blacksTurn_ = !cgs->blacksTurn_;
            // Remove my pawn from the previous position
            SetPieceAt(&nextCgs, srcRow, srcCol, NoPiece);
            // Remove opponents pawn that we take en-passe
            SetPieceAt(&nextCgs, enPasse.row_, enPasse.col_, NoPiece);
            // Put my pawn to the new position
            Position dstPos = MakePos(iamWhite ? 5 : 2, srcCol + (takeLeft ? -1 : +1), false);
            SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, piece);
            Move oppMove;
            if (!GetCheckState(&nextCgs, iamWhite).isCheck_)
            {
              Move oppMove;
              if (iamDeterm)
              {
                const int8_t outcome = -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
                if (outcome > bestOutcome)
                {
                  bestOutcome = outcome;
                  *bestMove = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
                  if (bestOutcome >= 1)
                  {
                    return bestOutcome;
                  }
                }
              }
              else
              {
                const bool choose = nondet_bool();
                *bestMove = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
                nondetHadMove = true;
                if (choose)
                {
                  return -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
                }
              }
            }
          }
        }
        // Normal pawn moves front, and takes left and right; with promotions!
        for (int8_t dc=-1; dc<=1; dc++) {
          const Position dstPos = MakePos(iamWhite ? srcRow+1 : srcRow-1, srcCol+dc, false);
          const ChessPiece aimPiece = GetPieceAt(cgs, dstPos.row_, dstPos.col_);
          if (aimPiece != NoPiece && IsWhitePiece(aimPiece) == iamWhite)
          {
            // My other piece prevents this my pawn from moving there
            continue;
          }
          if ( (dc == 0 && aimPiece == NoPiece) || (dc != 0 && IsWhitePiece(aimPiece) != iamWhite) ) {
            ChessGameState nextCgs = *cgs;
            nextCgs.blacksTurn_ = !cgs->blacksTurn_;
            // Remove my pawn from the old position
            SetPieceAt(&nextCgs, srcRow, srcCol, NoPiece);
            // Put my pawn to the new position
            SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, piece);
            // Promoted piece selection doesn't influence when it serves as an obstacle to a check to me
            if (!GetCheckState(&nextCgs, iamWhite).isCheck_)
            {
              if (dstPos.row_ == 0 || dstPos.row_ == 7) {
                // Try all kinds of promotions
                const int8_t *pPromos = (iamWhite ? cWhitePromos : cBlackPromos);
                for (int8_t iPromo=0; iPromo<4; iPromo++)
                {
                  const ChessPiece promotion = pPromos[iPromo];
                  SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, promotion);
                  Move oppMove;
                  if (iamDeterm)
                  {
                    const int8_t outcome = -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
                    if (outcome > bestOutcome)
                    {
                      bestOutcome = outcome;
                      *bestMove = MakeMovePromo(srcRow, srcCol, dstPos.row_, dstPos.col_, iPromo);
                      if (bestOutcome >= 1)
                      {
                        return bestOutcome;
                      }
                    }
                  }
                  else
                  {
                    const bool choose = nondet_bool();
                    *bestMove = MakeMovePromo(srcRow, srcCol, dstPos.row_, dstPos.col_, iPromo);
                    nondetHadMove = true;
                    if (choose)
                    {
                      return -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
                    }
                  }
                }
              }
              else
              {
                Move oppMove;
                if (iamDeterm)
                {
                  const int8_t outcome = -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
                  if (outcome > bestOutcome)
                  {
                    bestOutcome = outcome;
                    *bestMove = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
                    if (bestOutcome >= 1)
                    {
                      return bestOutcome;
                    }
                  }
                }
                else
                {
                  const bool choose = nondet_bool();
                  *bestMove = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
                  nondetHadMove = true;
                  if (choose)
                  {
                    return -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
                  }
                }
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
        nextCgs.blacksTurn_ = !cgs->blacksTurn_;
        // Remove this knight from the old position
        SetPieceAt(&nextCgs, srcRow, srcCol, NoPiece);
        for (int8_t iDir=0; iDir<8; iDir++)
        {
          const Position dstPos = MakePos(srcRow + cKnightDirs[iDir][0], srcCol + cKnightDirs[iDir][1], false);
          const ChessPiece aimPiece = GetPieceAt(cgs, dstPos.row_, dstPos.col_);
          if (aimPiece != NoPiece && IsWhitePiece(aimPiece) == iamWhite)
          {
            // My another piece prevents from moving there
            continue;
          }
          SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, piece);
          if (!GetCheckState(&nextCgs, iamWhite).isCheck_)
          {
            Move oppMove;
            if (iamDeterm)
            {
              const int8_t outcome = -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
              if (outcome > bestOutcome)
              {
                bestOutcome = outcome;
                *bestMove = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
                if (bestOutcome >= 1)
                {
                  return bestOutcome;
                }
              }
            }
            else
            {
              const bool choose = nondet_bool();
              *bestMove = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
              nondetHadMove = true;
              if (choose)
              {
                return -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
              }
            }
          }
          // epilogue - restore the aim piece that was there
          SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, aimPiece);
        }
        break;
      }
      case WhiteBishop:
      case BlackBishop:
      {
        ChessGameState nextCgs = *cgs;
        nextCgs.blacksTurn_ = !cgs->blacksTurn_;
        // Remove this bishop from the old position
        SetPieceAt(&nextCgs, srcRow, srcCol, NoPiece);
        for (int8_t iDir=0; iDir<4; iDir++)
        {
          for (int8_t dist=1; dist<=7; dist++)
          {
            const Position dstPos = MakePos(srcRow + dist * cBishopDirs[iDir][0], srcCol + dist * cBishopDirs[iDir][1], false);
            const ChessPiece aimPiece = GetPieceAt(&nextCgs, dstPos.row_, dstPos.col_);
            if (aimPiece != NoPiece && IsWhitePiece(aimPiece) == iamWhite)
            {
              // My other piece is an obstacle to further moving in this direction
              break;
            }
            SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, piece);
            if (!GetCheckState(&nextCgs, iamWhite).isCheck_)
            {
              Move oppMove;
              if (iamDeterm)
              {
                const int8_t outcome = -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
                if (outcome > bestOutcome)
                {
                  bestOutcome = outcome;
                  *bestMove = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
                  if (bestOutcome >= 1)
                  {
                    return bestOutcome;
                  }
                }
              }
              else
              {
                const bool choose = nondet_bool();
                *bestMove = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
                nondetHadMove = true;
                if (choose)
                {
                  return -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
                }
              }
            }
            // epilogue - restore the aim piece that was there
            SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, aimPiece);
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
        nextCgs.blacksTurn_ = !cgs->blacksTurn_;
        // Remove this rook from the old position
        SetPieceAt(&nextCgs, srcRow, srcCol, NoPiece);
        // TODO: forbid castling with this rook
        if (srcRow == 0 && srcCol == 0)
        {
          nextCgs.canWhite000_ = 0;
        }
        else if (srcRow == 0 && srcCol == 7)
        {
          nextCgs.canWhite00_ = 0;
        }
        else if (srcRow == 7 && srcCol == 0)
        {
          nextCgs.canBlack000_ = 0;
        }
        else if (srcRow == 7 && srcCol == 7)
        {
          nextCgs.canBlack00_ = 0;
        }
        for (int8_t iDir=0; iDir<4; iDir++)
        {
          for (int8_t dist=1; dist<=7; dist++)
          {
            const Position dstPos = MakePos(srcRow + dist * cRookDirs[iDir][0], srcCol + dist * cRookDirs[iDir][1], false);
            const ChessPiece aimPiece = GetPieceAt(&nextCgs, dstPos.row_, dstPos.col_);
            if (aimPiece != NoPiece && IsWhitePiece(aimPiece) == iamWhite)
            {
              // My other piece is an obstacle to further moving in this direction
              break;
            }
            SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, piece);
            if (!GetCheckState(&nextCgs, iamWhite).isCheck_)
            {
              Move oppMove;
              if (iamDeterm)
              {
                const int8_t outcome = -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
                if (outcome > bestOutcome)
                {
                  bestOutcome = outcome;
                  *bestMove = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
                  if (bestOutcome >= 1)
                  {
                    return bestOutcome;
                  }
                }
              }
              else
              {
                const bool choose = nondet_bool();
                *bestMove = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
                nondetHadMove = true;
                if (choose)
                {
                  return -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
                }
              }
            }
            // epilogue - restore the aim piece that was there
            SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, aimPiece);
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
        nextCgs.blacksTurn_ = !cgs->blacksTurn_;
        // Remove this queen from the old position
        SetPieceAt(&nextCgs, srcRow, srcCol, NoPiece);
        for (int8_t iDir=0; iDir<8; iDir++)
        {
          for (int8_t dist=1; dist<=7; dist++)
          {
            const Position dstPos = MakePos(srcRow + dist * cQueenDirs[iDir][0], srcCol + dist * cQueenDirs[iDir][1], false);
            const ChessPiece aimPiece = GetPieceAt(&nextCgs, dstPos.row_, dstPos.col_);
            if (aimPiece != NoPiece && IsWhitePiece(aimPiece) == iamWhite)
            {
              // My other piece is an obstacle to further moving in this direction
              break;
            }
            SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, piece);
            if (!GetCheckState(&nextCgs, iamWhite).isCheck_)
            {
              Move oppMove;
              if (iamDeterm)
              {
                const int8_t outcome = -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
                if (outcome > bestOutcome)
                {
                  bestOutcome = outcome;
                  *bestMove = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
                  if (bestOutcome >= 1)
                  {
                    return bestOutcome;
                  }
                }
              }
              else
              {
                const bool choose = nondet_bool();
                *bestMove = MakeMove(srcRow, srcCol, dstPos.row_, dstPos.col_);
                nondetHadMove = true;
                if (choose)
                {
                  return -Play(&nextCgs, !iamDeterm, MakePos(0, 0, false), &oppMove, depth + 1);
                }
              }
            }
            // epilogue - restore the aim piece that was there
            SetPieceAt(&nextCgs, dstPos.row_, dstPos.col_, aimPiece);
            if (aimPiece != NoPiece)
            {
              break;
            }
          }
        }
        break;
      }
      default:
        assert(piece == WhiteKing || piece == BlackKing);
      }
    }
  }
  if (bestOutcome == -2) // No moves detected
  {
    if (iamDeterm)
    {
      if (kingCheck.isCheck_)
      {
        // Deterministic, a check and no moves => mate (I lost)
        return -1;
      }
      else
      {
        // Deterministic, no check and no moves => stalemate
        return 0;
      }
    }
    else
    {
      if (!kingCheck.isCheck_ && !nondetHadMove)
      {
        // Non-deterministic, but no check and no move options appeared => stalemate
        return 0;
      }
      // Non-deterministic, but haven't selected any move => I surrendered
      return -1;
    }
  }
  return bestOutcome;
}

#include "V3Situation.h"

int main() {
  ChessGameState cgs;
  InitSituation(&cgs);
  Move firstMove;
  const int8_t whiteOutcome = Play(&cgs, true, MakePos(0, 0, false), &firstMove, 1);
  __CPROVER_assert(whiteOutcome >= 0, "Finding a move such that whites don't lose");
  return 0;
}
