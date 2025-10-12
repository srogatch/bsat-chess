#ifndef CHESS_STATE_H
#define CHESS_STATE_H

#include <stdint.h>

/* Piece encoding:
   0      : empty
   1..6   : White  (PAWN=1, KNIGHT=2, BISHOP=3, ROOK=4, QUEEN=5, KING=6)
   9..14  : Black  (PAWN=9, KNIGHT=10, BISHOP=11, ROOK=12, QUEEN=13, KING=14)
   (Black piece code = White piece code + 8)
*/
enum {
  EMPTY      = 0,
  W_PAWN     = 1, W_KNIGHT = 2, W_BISHOP = 3, W_ROOK = 4, W_QUEEN = 5, W_KING = 6,
  B_PAWN     = 9, B_KNIGHT = 10, B_BISHOP = 11, B_ROOK = 12, B_QUEEN = 13, B_KING = 14
};

typedef struct {
  /* Rows 0..7 from Black's back rank to White's back rank.
     Row 0: Black major pieces, Row 1: Black pawns, Row 6: White pawns, Row 7: White major pieces.
     White pawns move "up" the array (toward smaller row indices).
  */
  uint8_t board[8][8];

  /* En-passant target square *for the side to move now* (the square the capturing pawn will move to).
     If no en-passant is available, set ep_row = ep_col = -1.
  */
  int8_t  ep_row;  /* -1 or 0..7 */
  int8_t  ep_col;  /* -1 or 0..7 */

  /* 1 if White to move, 0 if Black to move. */
  uint8_t white_to_move;
} ChessState;

/* Helpers kept header-only for inlining (CBMC likes fewer call frames). */
static inline int is_white_piece(uint8_t p) { return p >= 1 && p <= 6; }
static inline int is_black_piece(uint8_t p) { return p >= 9 && p <= 14; }
static inline int piece_type(uint8_t p)     { return (int)(p & 7u); }   /* 0..6 with same mapping as white piece codes */
static inline int in_bounds(int r, int c)   { return (unsigned)r < 8u && (unsigned)c < 8u; }

/* Values in centipawns. King gets a very large value only to prioritize king captures as terminal. */
static const int PIECE_VALUE_BY_TYPE[7] = { 0, 100, 320, 330, 500, 900, 10000 };

/* Optional default starting position.
   If you define CHESS_STATE_NO_DEFAULTS before including this header, the variable is not defined.
   You can then define your own `ChessState g_state` elsewhere (e.g., with nondet contents for CBMC).
*/
#ifndef CHESS_STATE_NO_DEFAULTS
static ChessState g_state = {
  .board = {
    /* Row 0 (Black back rank) */
    { B_ROOK, B_KNIGHT, B_BISHOP, B_QUEEN, B_KING, B_BISHOP, B_KNIGHT, B_ROOK },
    /* Row 1 (Black pawns) */
    { B_PAWN, B_PAWN,   B_PAWN,   B_PAWN,  B_PAWN, B_PAWN,   B_PAWN,   B_PAWN },
    /* Row 2 */
    { EMPTY,  EMPTY,    EMPTY,    EMPTY,   EMPTY,  EMPTY,    EMPTY,    EMPTY  },
    /* Row 3 */
    { EMPTY,  EMPTY,    EMPTY,    EMPTY,   EMPTY,  EMPTY,    EMPTY,    EMPTY  },
    /* Row 4 */
    { EMPTY,  EMPTY,    EMPTY,    EMPTY,   EMPTY,  EMPTY,    EMPTY,    EMPTY  },
    /* Row 5 */
    { EMPTY,  EMPTY,    EMPTY,    EMPTY,   EMPTY,  EMPTY,    EMPTY,    EMPTY  },
    /* Row 6 (White pawns) */
    { W_PAWN, W_PAWN,   W_PAWN,   W_PAWN,  W_PAWN, W_PAWN,   W_PAWN,   W_PAWN },
    /* Row 7 (White back rank) */
    { W_ROOK, W_KNIGHT, W_BISHOP, W_QUEEN, W_KING, W_BISHOP, W_KNIGHT, W_ROOK }
  },
  .ep_row = -1,
  .ep_col = -1,
  .white_to_move = 1u
};
#endif /* CHESS_STATE_NO_DEFAULTS */

#endif /* CHESS_STATE_H */
