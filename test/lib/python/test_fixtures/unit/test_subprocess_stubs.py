from lib.python.test_fixtures.subprocess_stubs import make_stub_completed


def test_make_stub_completed_defaults_to_success() -> None:
    assert make_stub_completed().returncode == 0


def test_make_stub_completed_carries_stdout() -> None:
    assert make_stub_completed(stdout="out").stdout == "out"


def test_make_stub_completed_carries_stderr() -> None:
    assert make_stub_completed(stderr="bad").stderr == "bad"


def test_make_stub_completed_carries_returncode() -> None:
    assert make_stub_completed(returncode=2).returncode == 2
