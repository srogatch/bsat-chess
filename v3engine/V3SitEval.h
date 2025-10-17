void InitSituation(ChessGameState *cgs)
{
  cgs->blacksTurn_ = 0;
  cgs->canWhite00_ = 1;
  cgs->canWhite000_ = 1;
  cgs->canBlack00_ = 1;
  cgs->canBlack000_ = 1;
  for (int8_t i=2; i<=5; i++)
  {
    for (int8_t j=0; j<8; j++)
    {
      SetPieceAt(cgs, i, j, NoPiece,0);
    }
  }
  for (int8_t j=0; j<8; j++)
  {
    SetPieceAt(cgs, 1, j, WhitePawn,0);
  }
  for (int8_t j=0; j<8; j++)
  {
    SetPieceAt(cgs, 6, j, BlackPawn,0);
  }
  SetPieceAt(cgs, 0, 0, WhiteRook,0);
  SetPieceAt(cgs, 0, 1, WhiteKnight,0);
  SetPieceAt(cgs, 0, 2, WhiteBishop,0);
  SetPieceAt(cgs, 0, 3, WhiteQueen,0);
  SetPieceAt(cgs, 0, 4, WhiteKing,0);
  cgs->whiteKingRow_ = 0;
  cgs->whiteKingCol_ = 4;
  SetPieceAt(cgs, 0, 5, WhiteBishop,0);
  SetPieceAt(cgs, 0, 6, WhiteKnight,0);
  SetPieceAt(cgs, 0, 7, WhiteRook,0);

  SetPieceAt(cgs, 7, 0, BlackRook,0);
  SetPieceAt(cgs, 7, 1, BlackKnight,0);
  SetPieceAt(cgs, 7, 2, BlackBishop,0);
  SetPieceAt(cgs, 7, 3, BlackQueen,0);
  SetPieceAt(cgs, 7, 4, BlackKing,0);
  cgs->blackKingRow_ = 7;
  cgs->blackKingCol_ = 4;
  SetPieceAt(cgs, 7, 5, BlackBishop,0);
  SetPieceAt(cgs, 7, 6, BlackKnight,0);
  SetPieceAt(cgs, 7, 7, BlackRook,0);

  cgs->isEnpasse_ = 0;
  cgs->enPasseCol_ = 0;
}
