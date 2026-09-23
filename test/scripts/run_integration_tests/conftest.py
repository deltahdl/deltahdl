from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from unittest.mock import MagicMock, patch

import pytest

_RIT_INIT = (
    Path(__file__).resolve().parents[3]
    / "scripts" / "run_integration_tests" / "__init__.py"
)

CaseRun = tuple[list[str], tuple[bool, str]]


@pytest.fixture()
def rit(module_loader: Callable[[str, Path], ModuleType]) -> ModuleType:
    return module_loader("run_integration_tests", _RIT_INIT)


@pytest.fixture()
def run_case(
    module_loader: Callable[[str, Path], ModuleType], tmp_path: Path,
) -> Callable[[str, int, str, str], CaseRun]:
    runner = module_loader("run_integration_tests", _RIT_INIT)

    def _run(header: str, returncode: int, out: str, err: str) -> CaseRun:
        sv = tmp_path / "case.sv"
        sv.write_text(f"/*\n{header}*/\nmodule case_m; endmodule\n")
        seen: list[str] = []

        def fake_run(cmd: list[str], **_: object) -> MagicMock:
            seen.extend(cmd)
            return MagicMock(returncode=returncode, stdout=out, stderr=err)

        with patch.object(runner.subprocess, "run", side_effect=fake_run):
            outcome: tuple[bool, str] = runner.run_test(sv)
        return seen, outcome

    return _run
