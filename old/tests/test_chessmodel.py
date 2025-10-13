import csv
import ctypes
import io
import os
import subprocess
from pathlib import Path

import chess
import chess.pgn
import pytest


class MoveCat:
    InvalidMove = 0
    NormalMove = 1
    Stalemate = 2
    WhiteWon = 3
    BlackWon = 4


class Chessboard(ctypes.Structure):
    _fields_ = [("cells_", (ctypes.c_uint8 * 4) * 8)]


FIGURE_LOOKUP = {
    None: MoveCat.InvalidMove,  # placeholder for NoFig
    (chess.WHITE, chess.PAWN): 1,
    (chess.BLACK, chess.PAWN): 2,
    (chess.WHITE, chess.KNIGHT): 3,
    (chess.BLACK, chess.KNIGHT): 4,
    (chess.WHITE, chess.BISHOP): 5,
    (chess.BLACK, chess.BISHOP): 6,
    (chess.WHITE, chess.ROOK): 7,
    (chess.BLACK, chess.ROOK): 8,
    (chess.WHITE, chess.QUEEN): 9,
    (chess.BLACK, chess.QUEEN): 10,
    (chess.WHITE, chess.KING): 11,
    (chess.BLACK, chess.KING): 12,
}


def to_chessboard(board: chess.Board) -> Chessboard:
    cb = Chessboard()
    cells = cb.cells_
    # rows are 0 (rank 8) -> 7 (rank 1)
    for square, piece in board.piece_map().items():
        row = 7 - chess.square_rank(square)
        col = chess.square_file(square)
        col_pair = col // 2
        shift = (col % 2) * 4
        value = int(cells[row][col_pair])
        mask = 0xF << shift
        figure = FIGURE_LOOKUP[(piece.color, piece.piece_type)]
        value = (value & ~mask) | ((figure & 0xF) << shift)
        cells[row][col_pair] = value
    return cb


def expected_category(board: chess.Board) -> int:
    if board.is_checkmate():
        winner_color = not board.turn
        return MoveCat.WhiteWon if winner_color == chess.WHITE else MoveCat.BlackWon
    if board.is_stalemate():
        return MoveCat.Stalemate
    return MoveCat.NormalMove


def ensure_library(repo_root: Path) -> ctypes.CDLL:
    build_dir = repo_root / "build"
    build_dir.mkdir(exist_ok=True)
    lib_path = build_dir / "libchessmodel.so"
    src_path = repo_root / "model" / "ChessModel.c"
    if (
        not lib_path.exists()
        or lib_path.stat().st_mtime < src_path.stat().st_mtime
    ):
        subprocess.run(
            [
                "gcc",
                "-std=c11",
                "-O2",
                "-shared",
                "-fPIC",
                "-o",
                str(lib_path),
                str(src_path),
            ],
            check=True,
            cwd=repo_root,
        )
    lib = ctypes.CDLL(str(lib_path))
    lib.CategorizeMove.argtypes = [
        ctypes.POINTER(Chessboard),
        ctypes.POINTER(Chessboard),
    ]
    lib.CategorizeMove.restype = ctypes.c_int
    return lib


@pytest.mark.slow
def test_dataset_transitions():
    repo_root = Path(__file__).resolve().parents[1]
    dataset_path = repo_root / "datasets" / "club_games_data.csv"
    assert dataset_path.exists(), "Dataset file is missing"

    lib = ensure_library(repo_root)

    total_games = 0
    total_moves = 0

    with dataset_path.open(newline="") as csv_file:
        reader = csv.DictReader(csv_file)
        for game_index, row in enumerate(reader, start=1):
            pgn_text = row["pgn"].strip()
            if not pgn_text:
                pytest.fail(f"Empty PGN entry at dataset row {game_index}")
            game = chess.pgn.read_game(io.StringIO(pgn_text))
            assert game is not None, f"Invalid PGN at dataset row {game_index}"
            board = game.board()

            for ply_index, move in enumerate(game.mainline_moves(), start=1):
                from_cb = to_chessboard(board)
                board.push(move)
                to_cb = to_chessboard(board)
                result = lib.CategorizeMove(
                    ctypes.byref(from_cb),
                    ctypes.byref(to_cb),
                )
                rules = row.get("rules", "").lower()
                if rules and rules not in {"chess", "chess960"}:
                    total_moves += 1
                    continue
                expected = expected_category(board)
                assert (
                    result == expected
                ), (
                    f"Row {game_index}, ply {ply_index}: "
                    f"expected {expected}, got {result}"
                )
                total_moves += 1

            total_games += 1

    assert total_games > 0
    assert total_moves > 0
