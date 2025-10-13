# Repository Guidelines

## Project Structure & Module Organization
- `v3engine/`: Primary CBMC-friendly chess engine (`V3Chess.c`) plus board bootstrap (`V3Situation.h`). Everything needed for formal analysis lives here.
- `tools/`: Python helpers such as `write_situation.py` for emitting C snapshots when you need fixtures outside the default start position.
- `tests/`: Pytest suite; `test_chessmodel.py` remains the regression harness for replaying full games against the dataset.
- `datasets/`: Holds the PGN-derived CSV inputs. Keep `club_games_data.csv` and its ZIP side-by-side for reproducibility.
- `build/`: Destination for compiled artifacts (`build/v3engine`, shared libs, CBMC traces). Safe to wipe when rebuilding.

## Build, Test, and Development Commands
- `gcc -std=c11 -Wall -Wextra -DNDEBUG -o build/v3engine v3engine/V3Chess.c`: Fast sanity build of the CBMC target; keeps warnings visible.
- `cbmc v3engine/V3Chess.c --function main --bounds-check --pointer-check --unwind 6`: Typical bounded run; tune `--unwind` per scenario and capture traces under `build/`.
- `python3 tools/write_situation.py --fen "<FEN>" > v3engine/V3Situation.h`: Rebuild the starting position header from a FEN before specialised analyses.
- `pytest tests/test_chessmodel.py::test_dataset_transitions -q`: Full dataset replay (~4½ minutes). Run after modifying move logic.

## Coding Style & Naming Conventions
- C sources target C11; use two-space indentation, brace-on-new-line, and prefer `static` for file-local helpers. Keep loops explicitly bounded for CBMC (no open-ended `while` unless guarded with constants).
- Name enums and structs by chess role (`WhiteKnight`, `ChessGameState`); avoid magic numbers in move generators—introduce `static const` tables instead.
- Python utilities remain PEP 8 compliant with descriptive names and optional type hints when it clarifies expected structures.
- Regenerated headers should include a provenance comment (`// Auto-generated from ...`) to prevent manual edits.

## Testing Guidelines
- Treat CBMC as the first line of defense: run with `--unwind` values that cover the scenario you touched, and store counterexamples for future debugging.
- Pytest remains the acceptance layer; keep new tests under `tests/` with `test_*.py` naming. Mark long-running trials with `@pytest.mark.slow`.
- Rebuild `build/v3engine` (or the shared lib) before executing either CBMC or pytest to ensure bitfield changes are reflected.
- For smoke checks, script minimal positions via `tools/write_situation.py` and run CBMC on the resulting header.

## Commit & Pull Request Guidelines
- Use imperative, single-responsibility commits (“Clamp knight check handling”). Reference relevant CBMC traces or dataset fixtures when they motivate the change.
- Pull requests should recap rules affected, list commands executed (`gcc`, `cbmc`, `pytest`), and call out unwind-depth or dataset runtime changes. Attach CBMC traces when documenting fixes.
