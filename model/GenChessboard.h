#include <stdint.h>

static inline FigurePos MakeFigurePos(uint8_t row, uint8_t col, FigureTypes ft)
{
  FigurePos pos;
  pos.row_ = row;
  pos.col_ = col;
  pos.ft_ = (uint8_t)ft;
  return pos;
}

void PutInitial(ChessBoard *board)
{
  board->whoseTurn_ = WhitePlayer;

  board->whites_.kingPos_ = MakeFigurePos(7U, 4U, Knight);
  board->whites_.nFigs_ = 7U;
  board->whites_.nPawns_ = MAX_PAWNS;

  const FigurePos white_figs[7] = {
    MakeFigurePos(7U, 1U, Knight),
    MakeFigurePos(7U, 6U, Knight),
    MakeFigurePos(7U, 2U, Bishop),
    MakeFigurePos(7U, 5U, Bishop),
    MakeFigurePos(7U, 0U, Rook),
    MakeFigurePos(7U, 7U, Rook),
    MakeFigurePos(7U, 3U, Queen),
  };

  for (uint8_t idx = 0; idx < 7U; ++idx)
    board->whites_.fps_[idx] = white_figs[idx];

  for (uint8_t file = 0; file < MAX_PAWNS; ++file)
    board->whites_.fps_[7U + file] = MakeFigurePos(6U, file, Knight);

  board->blacks_.kingPos_ = MakeFigurePos(0U, 4U, Knight);
  board->blacks_.nFigs_ = 7U;
  board->blacks_.nPawns_ = MAX_PAWNS;

  const FigurePos black_figs[7] = {
    MakeFigurePos(0U, 1U, Knight),
    MakeFigurePos(0U, 6U, Knight),
    MakeFigurePos(0U, 2U, Bishop),
    MakeFigurePos(0U, 5U, Bishop),
    MakeFigurePos(0U, 0U, Rook),
    MakeFigurePos(0U, 7U, Rook),
    MakeFigurePos(0U, 3U, Queen),
  };

  for (uint8_t idx = 0; idx < 7U; ++idx)
    board->blacks_.fps_[idx] = black_figs[idx];

  for (uint8_t file = 0; file < MAX_PAWNS; ++file)
    board->blacks_.fps_[7U + file] = MakeFigurePos(1U, file, Knight);
}
