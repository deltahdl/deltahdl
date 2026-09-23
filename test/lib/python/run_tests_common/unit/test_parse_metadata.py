from pathlib import Path

from lib.python import run_tests_common


def test_extracts_all_fields(tmp_path: Path) -> None:
    sv = tmp_path / "test.sv"
    sv.write_text(
        "/*\n:name: foo\n:type: simulation elaboration parsing\n"
        ":tags: 7.3.2\n:should_fail_because: bad code\n*/\n"
        "module top; endmodule\n"
    )
    assert run_tests_common.parse_metadata(str(sv)) == {
        "name": "foo",
        "type": "simulation elaboration parsing",
        "tags": "7.3.2",
        "should_fail_because": "bad code",
    }


def test_returns_empty_dict_when_no_comment(tmp_path: Path) -> None:
    sv = tmp_path / "bare.sv"
    sv.write_text("module bare; endmodule\n")
    assert not run_tests_common.parse_metadata(str(sv))


def test_returns_empty_type_when_absent(tmp_path: Path) -> None:
    sv = tmp_path / "no_type.sv"
    sv.write_text("/*\n:name: no_type\n:tags: 5.10\n*/\nmodule m; endmodule\n")
    assert set(run_tests_common.parse_metadata(str(sv))) == {"name", "tags"}
