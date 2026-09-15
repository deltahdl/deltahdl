import json
import os
from collections.abc import Callable, Iterator
from types import ModuleType
from typing import Any

import pytest

from lib.python import claude_cli_streaming as _streaming


@pytest.fixture()
def streaming() -> ModuleType:
    return _streaming


@pytest.fixture()
def make_settings() -> Iterator[Callable[[list[str]], dict[str, Any]]]:
    paths: list[str] = []

    def _make(patterns: list[str]) -> dict[str, Any]:
        path = _streaming.write_deny_hook_settings(patterns)
        paths.append(path)
        with open(path, encoding="utf-8") as handle:
            data: dict[str, Any] = json.load(handle)
        return data

    yield _make

    for path in paths:
        os.unlink(path)
