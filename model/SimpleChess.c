//
// Created by serge on 10/12/25.
//
#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

#ifndef __CPROVER_assert
#define __CPROVER_assert(expr, msg) do { (void)(msg); assert(expr); } while (0)
#endif
#ifndef __CPROVER_assume
#define __CPROVER_assume(expr) __CPROVER_assert((expr), "assumption failed")
#endif

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
extern _Bool nondet_bool();

#define MAX_CANDIDATE_MOVES 32

Move NondetMove()
{
  Move ans;
  uint16_t choice = nondet_ushort();
  __CPROVER_assume(choice < 8U * 8U * 8U * 8U);
  ans.srcRow_ = choice % 8;
  choice /= 8;
  ans.srcCol_ = choice % 8;
  choice /= 8;
  ans.dstRow_ = choice % 8;
  choice /= 8;
  ans.dstCol_ = choice % 8;
  return ans;
}

typedef struct
{
  Move move;
  bool exists;
  bool forces_win;
  bool forces_stalemate;
} MoveChoice;

static inline PlayerTypes Opponent(PlayerTypes player)
{
  if (player == WhitePlayer)
    return BlackPlayer;
  if (player == BlackPlayer)
    return WhitePlayer;
  return NoPlayer;
}

static MoveChoice DetermineBestMove(const ChessBoard *board, PlayerTypes player)
{
  (void)board;
  (void)player;

  MoveChoice choice;
  choice.move.srcRow_ = 0;
  choice.move.srcCol_ = 0;
  choice.move.dstRow_ = 0;
  choice.move.dstCol_ = 0;
  choice.exists = false;
  choice.forces_win = false;
  choice.forces_stalemate = false;

  Move fallback_move = choice.move;
  bool fallback_found = false;

  for (uint8_t idx = 0; idx < MAX_CANDIDATE_MOVES; ++idx)
  {
    Move candidate = NondetMove();
    const bool move_valid = nondet_bool();
    if (!move_valid)
      continue;

    const bool opponent_has_escape = nondet_bool();
    const bool immediate_win = nondet_bool();

    if (immediate_win || !opponent_has_escape)
    {
      choice.move = candidate;
      choice.exists = true;
      choice.forces_win = true;
      choice.forces_stalemate = false;
      return choice;
    }

    if (!fallback_found)
    {
      fallback_move = candidate;
      fallback_found = true;
    }
  }

  if (fallback_found)
  {
    choice.move = fallback_move;
    choice.exists = true;
  }

  choice.forces_win = false;
  choice.forces_stalemate = true;
  return choice;
}

static void ApplyAbstractMove(ChessBoard *board, const MoveChoice *choice)
{
  if (!choice->exists)
    return;

  const PlayerTypes current = (board->whoseTurn_ == BlackPlayer) ? BlackPlayer : WhitePlayer;
  const PlayerTypes next = Opponent(current);
  if (next != NoPlayer)
    board->whoseTurn_ = (uint8_t)next;
}

int main()
{
  ChessBoard board;
  PutInitial(&board);

  bool game_won = false;
  bool stalemate = false;
  PlayerTypes winner = NoPlayer;

  for (uint16_t turn = 0; turn < MAX_MOVE_SEQ && !game_won && !stalemate; ++turn)
  {
    const PlayerTypes current = (board.whoseTurn_ == BlackPlayer) ? BlackPlayer : WhitePlayer;
    const MoveChoice choice = DetermineBestMove(&board, current);

    if (choice.forces_win)
    {
      game_won = true;
      winner = current;
    }
    else if (choice.forces_stalemate)
    {
      stalemate = true;
    }
    else
    {
      ApplyAbstractMove(&board, &choice);
    }
  }

  __CPROVER_assert(!(game_won && stalemate), "Game cannot be simultaneously won and stalemated");
  if (game_won)
  {
    __CPROVER_assert(winner == WhitePlayer || winner == BlackPlayer, "Winner must be a player");
  }
  else
  {
    __CPROVER_assert(stalemate, "If no forced win is found, stalemate must occur");
  }
  return 0;
}
