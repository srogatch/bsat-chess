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
      SetPieceAt(cgs, i, j, NoPiece, false);
    }
  }
  for (int8_t j=0; j<8; j++)
  {
    SetPieceAt(cgs, 1, j, WhitePawn, false);
  }
  for (int8_t j=0; j<8; j++)
  {
    SetPieceAt(cgs, 6, j, BlackPawn, false);
  }
  SetPieceAt(cgs, 0, 0, WhiteRook, false);
  SetPieceAt(cgs, 0, 1, WhiteKnight, false);
  SetPieceAt(cgs, 0, 2, WhiteBishop, false);
  SetPieceAt(cgs, 0, 3, WhiteQueen, false);
  SetPieceAt(cgs, 0, 4, WhiteKing, false);
  cgs->whiteKingRow_ = 0;
  cgs->whiteKingCol_ = 4;
  SetPieceAt(cgs, 0, 5, WhiteBishop, false);
  SetPieceAt(cgs, 0, 6, WhiteKnight, false);
  SetPieceAt(cgs, 0, 7, WhiteRook, false);

  SetPieceAt(cgs, 7, 0, BlackRook, false);
  SetPieceAt(cgs, 7, 1, BlackKnight, false);
  SetPieceAt(cgs, 7, 2, BlackBishop, false);
  SetPieceAt(cgs, 7, 3, BlackQueen, false);
  SetPieceAt(cgs, 7, 4, BlackKing, false);
  cgs->blackKingRow_ = 7;
  cgs->blackKingCol_ = 4;
  SetPieceAt(cgs, 7, 5, BlackBishop, false);
  SetPieceAt(cgs, 7, 6, BlackKnight, false);
  SetPieceAt(cgs, 7, 7, BlackRook, false);
}
