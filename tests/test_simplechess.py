import csv
import ctypes
import io
import subprocess
from enum import IntEnum
from pathlib import Path

import chess
import chess.pgn
import pytest


class Chessboard(ctypes.Structure):
    _fields_ = [("cells_", (ctypes.c_uint8 * 4) * 8)]


class EnPassantInfo(ctypes.Structure):
    _fields_ = [
        ("available", ctypes.c_bool),
        ("row", ctypes.c_int),
        ("col", ctypes.c_int),
    ]


COLOR_WHITE = 0
COLOR_BLACK = 1


class SimpleOutcome(IntEnum):
    DRAW = 0
    WHITE = 1
    BLACK = 2


def to_chessboard(board: chess.Board) -> Chessboard:
    cb = Chessboard()
    cells = cb.cells_
    for square, piece in board.piece_map().items():
        row = 7 - chess.square_rank(square)
        col = chess.square_file(square)
        col_pair = col // 2
        shift = (col % 2) * 4
        value = int(cells[row][col_pair])
        mask = 0xF << shift
        figure = _figure_lookup(piece)
        value = (value & ~mask) | ((figure & 0xF) << shift)
        cells[row][col_pair] = value
    return cb


def _figure_lookup(piece: chess.Piece) -> int:
    color = COLOR_WHITE if piece.color == chess.WHITE else COLOR_BLACK
    base = {
        chess.PAWN: 1,
        chess.KNIGHT: 3,
        chess.BISHOP: 5,
        chess.ROOK: 7,
        chess.QUEEN: 9,
        chess.KING: 11,
    }[piece.piece_type]
    return base if color == COLOR_WHITE else base + 1


def ensure_simple_library(repo_root: Path) -> ctypes.CDLL:
    build_dir = repo_root / "build"
    build_dir.mkdir(exist_ok=True)
    lib_path = build_dir / "libsimplechess.so"
    sources = [
        repo_root / "model" / "SimpleChess.c",
        repo_root / "model" / "ChessModel.c",
    ]
    if (
        not lib_path.exists()
        or any(lib_path.stat().st_mtime < src.stat().st_mtime for src in sources)
    ):
        subprocess.run(
            [
                "gcc",
                "-std=c11",
                "-O2",
                "-shared",
                "-fPIC",
                "-DSIMPLE_CHESS_LIBRARY",
                "-o",
                str(lib_path),
                *(str(src) for src in sources),
            ],
            check=True,
            cwd=repo_root,
        )
    lib = ctypes.CDLL(str(lib_path))
    lib.SimpleChess_EvaluateOutcome.argtypes = [
        ctypes.POINTER(Chessboard),
        ctypes.c_int,
        ctypes.POINTER(EnPassantInfo),
        ctypes.c_int,
    ]
    lib.SimpleChess_EvaluateOutcome.restype = ctypes.c_int
    return lib


@pytest.mark.slow
def test_simplechess_evaluates_terminal_positions():
    repo_root = Path(__file__).resolve().parents[1]
    dataset_path = repo_root / "datasets" / "club_games_data.csv"
    assert dataset_path.exists(), "Dataset file is missing"

    lib = ensure_simple_library(repo_root)

    matched_positions = 0
    with dataset_path.open(newline="") as csv_file:
        reader = csv.DictReader(csv_file)
        for row_index, row in enumerate(reader, start=1):
            pgn_text = row["pgn"].strip()
            if not pgn_text:
                continue
            game = chess.pgn.read_game(io.StringIO(pgn_text))
            if game is None:
                continue
            board = game.board()
            rules = row.get("rules", "").lower()
            if rules and rules not in {"chess", "chess960"}:
                continue
            for move in game.mainline_moves():
                board.push(move)
                if not (board.is_checkmate() or board.is_stalemate()):
                    continue

                cb = to_chessboard(board)
                color_to_move = COLOR_WHITE if board.turn == chess.WHITE else COLOR_BLACK
                outcome = lib.SimpleChess_EvaluateOutcome(
                    ctypes.byref(cb),
                    color_to_move,
                    None,
                    2,
                )
                if board.is_checkmate():
                    winner = COLOR_WHITE if not board.turn else COLOR_BLACK
                    expected = (
                        SimpleOutcome.WHITE if winner == COLOR_WHITE else SimpleOutcome.BLACK
                    )
                else:
                    expected = SimpleOutcome.DRAW
                assert (
                    outcome == expected.value
                ), f"Row {row_index}: expected {expected}, got {outcome}"
                matched_positions += 1

    assert matched_positions > 0, "No terminal positions evaluated"
