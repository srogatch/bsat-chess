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

static inline int is_white_piece(uint8_t p) { return p >= 1 && p <= 6; }
static inline int is_black_piece(uint8_t p) { return p >= 9 && p <= 14; }
static inline int piece_type(uint8_t p)     { return (int)(p & 7u); } /* 0..6 with same mapping as white codes */
static inline int in_bounds(int r, int c)   { return (unsigned)r < 8u && (unsigned)c < 8u; }

/* Values in centipawns. */
static const int PIECE_VALUE_BY_TYPE[7] = { 0, 100, 320, 330, 500, 900, 20000 };

enum {
  BOARD_DIM = 8,
  BOARD_SQUARES = BOARD_DIM * BOARD_DIM,
  MAX_PIECES_PER_SIDE = 16
};

typedef struct {
  uint8_t count;
  uint8_t piece[MAX_PIECES_PER_SIDE];
  int8_t row[MAX_PIECES_PER_SIDE];
  int8_t col[MAX_PIECES_PER_SIDE];
} PieceList;

/* Castling rights bitfield */
enum {
  CR_WK = 1u,  /* White can castle king-side */
  CR_WQ = 2u,  /* White can castle queen-side */
  CR_BK = 4u,  /* Black can castle king-side */
  CR_BQ = 8u   /* Black can castle queen-side */
};

/* Game status codes (for inspection by a harness if you wish). */
enum {
  GAME_ONGOING  = 0,
  GAME_CHECKMATE= 1,
  GAME_STALEMATE= 2
};

typedef struct {
  /* Rows 0..7 from Black back rank to White back rank. */
  uint8_t board[8][8];

  /* En-passant target square for the side to move now; -1/-1 if none. */
  int8_t  ep_row;               /* -1 or 0..7 */
  int8_t  ep_col;               /* -1 or 0..7 */

  /* Side to move: 1=White, 0=Black. */
  uint8_t white_to_move;

  /* Castling rights: CR_* bits. */
  uint8_t castle_rights;

  /* King positions to avoid scanning the board. -1 if captured (shouldn’t happen in legal play). */
  int8_t  w_king_r, w_king_c;
  int8_t  b_king_r, b_king_c;
  PieceList white_pieces;
  PieceList black_pieces;
  uint64_t white_attacks;
  uint64_t black_attacks;
  uint8_t attacks_valid;
} ChessState;

/* Optional default starting position. */
#ifndef CHESS_STATE_NO_DEFAULTS
static ChessState g_state = {
  .board = {
    { B_ROOK, B_KNIGHT, B_BISHOP, B_QUEEN, B_KING, B_BISHOP, B_KNIGHT, B_ROOK }, /* row 0 */
    { B_PAWN, B_PAWN,   B_PAWN,   B_PAWN,  B_PAWN, B_PAWN,   B_PAWN,   B_PAWN }, /* row 1 */
    { EMPTY,  EMPTY,    EMPTY,    EMPTY,   EMPTY,  EMPTY,    EMPTY,    EMPTY  }, /* row 2 */
    { EMPTY,  EMPTY,    EMPTY,    EMPTY,   EMPTY,  EMPTY,    EMPTY,    EMPTY  }, /* row 3 */
    { EMPTY,  EMPTY,    EMPTY,    EMPTY,   EMPTY,  EMPTY,    EMPTY,    EMPTY  }, /* row 4 */
    { EMPTY,  EMPTY,    EMPTY,    EMPTY,   EMPTY,  EMPTY,    EMPTY,    EMPTY  }, /* row 5 */
    { W_PAWN, W_PAWN,   W_PAWN,   W_PAWN,  W_PAWN, W_PAWN,   W_PAWN,   W_PAWN }, /* row 6 */
    { W_ROOK, W_KNIGHT, W_BISHOP, W_QUEEN, W_KING, W_BISHOP, W_KNIGHT, W_ROOK }  /* row 7 */
  },
  .ep_row = -1, .ep_col = -1,
  .white_to_move = 1u,
  .castle_rights = (CR_WK|CR_WQ|CR_BK|CR_BQ),
  .w_king_r = 7, .w_king_c = 4,
  .b_king_r = 0, .b_king_c = 4,
  .white_pieces = {
    .count = 16,
    .piece = {
      W_ROOK, W_KNIGHT, W_BISHOP, W_QUEEN, W_KING, W_BISHOP, W_KNIGHT, W_ROOK,
      W_PAWN, W_PAWN, W_PAWN, W_PAWN, W_PAWN, W_PAWN, W_PAWN, W_PAWN
    },
    .row = {
      7,7,7,7,7,7,7,7,
      6,6,6,6,6,6,6,6
    },
    .col = {
      0,1,2,3,4,5,6,7,
      0,1,2,3,4,5,6,7
    }
  },
  .black_pieces = {
    .count = 16,
    .piece = {
      B_ROOK, B_KNIGHT, B_BISHOP, B_QUEEN, B_KING, B_BISHOP, B_KNIGHT, B_ROOK,
      B_PAWN, B_PAWN, B_PAWN, B_PAWN, B_PAWN, B_PAWN, B_PAWN, B_PAWN
    },
    .row = {
      0,0,0,0,0,0,0,0,
      1,1,1,1,1,1,1,1
    },
    .col = {
      0,1,2,3,4,5,6,7,
      0,1,2,3,4,5,6,7
    }
  },
  .white_attacks = 0ull,
  .black_attacks = 0ull,
  .attacks_valid = 0u
};
#endif

#endif /* CHESS_STATE_H */
