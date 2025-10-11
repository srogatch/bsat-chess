# Repository Guidelines

## Project Structure & Module Organization
- `model/`: C sources for the core chess engine (`ChessModel.c`) and generated position snapshot (`Situation.h`). The `main` function is only for quick inspection of a position’s legal moves.
- `tools/`: Python utilities, notably `write_situation.py`, which emits `model/Situation.h` from a python-chess board.
- `tests/`: Pytest suite (`test_chessmodel.py`) that replays PGNs from the dataset and checks move categorization.
- `datasets/`: Input data used by tests. `club_games_data.csv` is required; keep the ZIP archived alongside it for provenance.
- `build/`: Compiled artifacts such as `libchessmodel.so`; safe to clean and regenerate.

## Build, Test, and Development Commands
- `python3 tools/write_situation.py --fen "<FEN>"`: Generate `Situation.h` for a specific position. Use `--pgn <file> --game-index N --ply M` to snapshot deeper in a game.
- `gcc -std=c11 -O2 -shared -fPIC -o build/libchessmodel.so model/ChessModel.c`: Build the shared library used by tests.
- `pytest tests/test_chessmodel.py::test_dataset_transitions -q`: Replays every move in the dataset (~4½ minutes); run before publishing changes.

## Coding Style & Naming Conventions
- C code is ANSI C11 with two-space indentation, braces on new lines, and explicit helper functions. Prefer `static` for internal linkage and keep enums synchronized with `python-chess` consumers.
- Python utilities follow PEP 8; use descriptive function names (`load_board_from_pgn`) and type hints where practical.
- Generated files should include a header comment stating their provenance.

## Testing Guidelines
- Primary framework: `pytest`. Keep new tests under `tests/` and name files `test_*.py`.
- Always rebuild the shared library before running the suite if `ChessModel.c` changes.
- Slow dataset test is the authoritative regression check; smaller unit tests are welcome for focused logic.

## Commit & Pull Request Guidelines
- Write commits in imperative mood (“Add en-passant guard”), scoped to a single concern. Reference dataset or tooling changes explicitly.
- PRs should summarize chess rule coverage, list verification commands, and link issues. Include notes on performance impacts (e.g., dataset replay duration) and any new tooling usage.
