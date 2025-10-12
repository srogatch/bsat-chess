#include <stdint.h>
#include <assert.h>
#include <stdbool.h>

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
