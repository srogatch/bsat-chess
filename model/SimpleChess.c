#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "ChessEngine.h"
#include "GenChessboard.h"

#define MAX_MOVE_SEQ 256
// Limit recursive exploration to a manageable ply depth while staying within MAX_MOVE_SEQ.
#define MAX_SEARCH_DEPTH 6

typedef enum {
  SimpleOutcomeDraw = 0,
  SimpleOutcomeWhiteWin = 1,
  SimpleOutcomeBlackWin = 2
} SimpleOutcome;

typedef struct {
  Chessboard board;
  int whose_turn;
  EnPassantInfo ep_info;
} GameState;

#ifndef SIMPLE_CHESS_LIBRARY
typedef struct {
  MoveDesc move;
  SimpleOutcome outcome;
  bool has_move;
} BestMoveResult;
#endif

static inline bool OutcomeIsWinFor(SimpleOutcome outcome, int color) {
  if (outcome == SimpleOutcomeDraw)
    return false;
  if (color == ColorWhite)
    return outcome == SimpleOutcomeWhiteWin;
  return outcome == SimpleOutcomeBlackWin;
}

static inline bool OutcomeIsLossFor(SimpleOutcome outcome, int color) {
  if (outcome == SimpleOutcomeDraw)
    return false;
  if (color == ColorWhite)
    return outcome == SimpleOutcomeBlackWin;
  return outcome == SimpleOutcomeWhiteWin;
}

#ifndef SIMPLE_CHESS_LIBRARY
static inline int OutcomeScore(SimpleOutcome outcome, int color) {
  if (OutcomeIsWinFor(outcome, color))
    return 1;
  if (OutcomeIsLossFor(outcome, color))
    return -1;
  return 0;
}

static inline bool OutcomeBetter(SimpleOutcome lhs, SimpleOutcome rhs, int color) {
  const int lhs_score = OutcomeScore(lhs, color);
  const int rhs_score = OutcomeScore(rhs, color);
  return lhs_score > rhs_score;
}
#endif

static EnPassantInfo ComputeNextEnPassant(const Chessboard *board, const MoveDesc *mv) {
  EnPassantInfo info = {false, 0, 0};
  const Figure moved = FigAt(board, mv->src_row, mv->src_col);
  if (FigPiece(moved) == PiecePawn) {
    const int delta = mv->dst_row - mv->src_row;
    if (delta == 2 || delta == -2) {
      info.available = true;
      info.row = (mv->src_row + mv->dst_row) / 2;
      info.col = mv->src_col;
      return info;
    }
  }
  return info;
}

static SimpleOutcome EvaluatePosition(const GameState *state, int depth_left);

#ifndef SIMPLE_CHESS_LIBRARY
static BestMoveResult FindBestMove(const GameState *state, int depth_left) {
  BestMoveResult result;
  result.has_move = false;
  result.outcome = (state->whose_turn == ColorWhite) ? SimpleOutcomeBlackWin : SimpleOutcomeWhiteWin;

  const EnPassantInfo *ep_ptr = state->ep_info.available ? &state->ep_info : NULL;
  MoveDesc moves[MAX_LEGAL_MOVES];
  const int move_count = Chess_GenerateLegalMoves(&state->board,
                                                  state->whose_turn,
                                                  state->ep_info.available,
                                                  ep_ptr,
                                                  moves,
                                                  MAX_LEGAL_MOVES);
  if (move_count <= 0)
    return result;

  for (int idx = 0; idx < move_count && idx < MAX_LEGAL_MOVES; ++idx) {
    GameState next_state;
    Chess_ApplyMove(&state->board, &next_state.board, &moves[idx]);
    next_state.whose_turn = 1 - state->whose_turn;
    next_state.ep_info = ComputeNextEnPassant(&state->board, &moves[idx]);
    const SimpleOutcome outcome = EvaluatePosition(&next_state, depth_left - 1);

    if (!result.has_move || OutcomeBetter(outcome, result.outcome, state->whose_turn)) {
      result.move = moves[idx];
      result.outcome = outcome;
      result.has_move = true;
    }

    if (OutcomeIsWinFor(outcome, state->whose_turn))
      break;
  }

  return result;
}
#endif

static SimpleOutcome EvaluatePosition(const GameState *state, int depth_left) {
  const EnPassantInfo *ep_ptr = state->ep_info.available ? &state->ep_info : NULL;
  MoveDesc moves[MAX_LEGAL_MOVES];
  const int move_count = Chess_GenerateLegalMoves(&state->board,
                                                  state->whose_turn,
                                                  state->ep_info.available,
                                                  ep_ptr,
                                                  moves,
                                                  MAX_LEGAL_MOVES);

  if (move_count <= 0) {
    if (Chess_KingInCheck(&state->board, state->whose_turn)) {
      return (state->whose_turn == ColorWhite) ? SimpleOutcomeBlackWin : SimpleOutcomeWhiteWin;
    }
    return SimpleOutcomeDraw;
  }

  if (depth_left <= 0)
    return SimpleOutcomeDraw;

  bool has_draw = false;
  const int color = state->whose_turn;

  for (int idx = 0; idx < move_count && idx < MAX_LEGAL_MOVES; ++idx) {
    GameState next_state;
    Chess_ApplyMove(&state->board, &next_state.board, &moves[idx]);
    next_state.whose_turn = 1 - color;
    next_state.ep_info = ComputeNextEnPassant(&state->board, &moves[idx]);

    const SimpleOutcome outcome = EvaluatePosition(&next_state, depth_left - 1);
    if (OutcomeIsWinFor(outcome, color))
      return outcome;
    if (outcome == SimpleOutcomeDraw)
      has_draw = true;
  }

  if (has_draw)
    return SimpleOutcomeDraw;

  return (color == ColorWhite) ? SimpleOutcomeBlackWin : SimpleOutcomeWhiteWin;
}

int SimpleChess_EvaluateOutcome(const Chessboard *board,
                                int color,
                                const EnPassantInfo *ep_info,
                                int depth) {
  GameState state;
  state.board = *board;
  state.whose_turn = color;
  if (ep_info) {
    state.ep_info = *ep_info;
  } else {
    state.ep_info.available = false;
    state.ep_info.row = 0;
    state.ep_info.col = 0;
  }
  if (depth < 0)
    depth = 0;
  if (depth > MAX_SEARCH_DEPTH)
    depth = MAX_SEARCH_DEPTH;
  const SimpleOutcome outcome = EvaluatePosition(&state, depth);
  return (int)outcome;
}

#ifndef SIMPLE_CHESS_LIBRARY
int main(void) {
  GameState state;
  PutInitial(&state.board);
  state.whose_turn = ColorWhite;
  state.ep_info.available = false;
  state.ep_info.row = 0;
  state.ep_info.col = 0;

  SimpleOutcome final_outcome = SimpleOutcomeDraw;

  for (int ply = 0; ply < MAX_MOVE_SEQ; ++ply) {
    BestMoveResult best = FindBestMove(&state, MAX_SEARCH_DEPTH);
    if (!best.has_move) {
      if (Chess_KingInCheck(&state.board, state.whose_turn)) {
        final_outcome = (state.whose_turn == ColorWhite) ? SimpleOutcomeBlackWin : SimpleOutcomeWhiteWin;
      } else {
        final_outcome = SimpleOutcomeDraw;
      }
      break;
    }
    if (OutcomeIsWinFor(best.outcome, state.whose_turn)) {
      final_outcome = best.outcome;
      break;
    }
    if (best.outcome == SimpleOutcomeDraw) {
      final_outcome = SimpleOutcomeDraw;
      break;
    }

    Chessboard next_board;
    Chess_ApplyMove(&state.board, &next_board, &best.move);
    state.ep_info = ComputeNextEnPassant(&state.board, &best.move);
    state.board = next_board;
    state.whose_turn = 1 - state.whose_turn;
  }

  (void)final_outcome;
  return 0;
}
#endif
