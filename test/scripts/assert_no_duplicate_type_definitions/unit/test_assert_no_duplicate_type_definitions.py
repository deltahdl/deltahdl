import runpy
from collections.abc import Callable
from pathlib import Path
from types import ModuleType

import pytest


def test_a_line_comment_is_blanked(andt: ModuleType) -> None:
    assert "class" not in andt.strip_comments_and_strings("int x;  // class C {\n")


def test_a_block_comment_is_blanked(andt: ModuleType) -> None:
    assert "struct" not in andt.strip_comments_and_strings("/* struct S { */ int x;")


def test_a_block_comment_keeps_its_newlines(andt: ModuleType) -> None:
    stripped = andt.strip_comments_and_strings("/* a\nb\nc */\nclass C {\n")
    assert stripped.splitlines()[3].strip() == "class C {"


def test_a_string_literal_is_blanked(andt: ModuleType) -> None:
    assert "{" not in andt.strip_comments_and_strings('const char* s = "{";')


def test_an_escaped_quote_does_not_end_a_literal(andt: ModuleType) -> None:
    assert "{" not in andt.strip_comments_and_strings('const char* s = "a\\"{";')


def test_an_unterminated_block_comment_reaches_the_end(andt: ModuleType) -> None:
    assert andt.strip_comments_and_strings("int x; /* class C {").strip() == "int x;"


def test_an_unterminated_literal_reaches_the_end(andt: ModuleType) -> None:
    assert "{" not in andt.strip_comments_and_strings('const char* s = "{')


def test_code_either_side_of_a_comment_is_not_joined(andt: ModuleType) -> None:
    assert andt.strip_comments_and_strings("a/*x*/b") == "a     b"


def test_a_class_definition_is_found(andt: ModuleType) -> None:
    assert andt.definitions("class Frame {\n};\n") == [("", "Frame", 1)]


def test_a_struct_definition_is_found(andt: ModuleType) -> None:
    assert andt.definitions("struct Pair {\n};\n") == [("", "Pair", 1)]


def test_a_union_definition_is_found(andt: ModuleType) -> None:
    assert andt.definitions("union Slot {\n};\n") == [("", "Slot", 1)]


def test_an_enum_class_definition_is_found(andt: ModuleType) -> None:
    assert andt.definitions("enum class Severity : uint8_t {\n};\n") == [
        ("", "Severity", 1),
    ]


def test_a_plain_enum_definition_is_found(andt: ModuleType) -> None:
    assert andt.definitions("enum Colour {\n};\n") == [("", "Colour", 1)]


def test_a_forward_declaration_is_not_a_definition(andt: ModuleType) -> None:
    assert andt.definitions("class Frame;\n") == []


def test_a_variable_of_a_struct_type_is_not_a_definition(andt: ModuleType) -> None:
    assert andt.definitions("struct Frame frame;\n") == []


def test_a_base_clause_may_put_the_brace_on_a_later_line(andt: ModuleType) -> None:
    assert andt.definitions("class Frame\n    : public Base {\n};\n") == [
        ("", "Frame", 1),
    ]


def test_a_head_with_no_brace_or_semicolon_is_not_a_definition(andt: ModuleType) -> None:
    assert andt.definitions("class Frame\n") == []


def test_a_template_specialization_is_not_a_definition(andt: ModuleType) -> None:
    assert andt.definitions("template <>\nstruct Traits<int> {\n};\n") == []


def test_a_template_definition_is_found(andt: ModuleType) -> None:
    assert andt.definitions("template <typename T> struct Traits {\n};\n") == [
        ("", "Traits", 1),
    ]


def test_the_namespace_is_recorded(andt: ModuleType) -> None:
    assert andt.definitions("namespace delta {\nclass Frame {\n};\n}\n") == [
        ("delta", "Frame", 2),
    ]


def test_a_nested_namespace_is_joined(andt: ModuleType) -> None:
    assert andt.definitions("namespace a::b {\nclass F {\n};\n}\n") == [
        ("a::b", "F", 2),
    ]


def test_two_namespace_lines_are_joined(andt: ModuleType) -> None:
    text = "namespace a {\nnamespace b {\nclass F {\n};\n}\n}\n"
    assert andt.definitions(text) == [("a::b", "F", 3)]


def test_an_anonymous_namespace_is_named(andt: ModuleType) -> None:
    assert andt.definitions("namespace {\nclass F {\n};\n}\n") == [
        ("(anonymous)", "F", 2),
    ]


def test_a_definition_after_a_namespace_closes_is_at_the_outer_scope(andt: ModuleType) -> None:
    text = "namespace a {\n}\nclass F {\n};\n"
    assert andt.definitions(text) == [("", "F", 3)]


def test_a_type_nested_in_a_class_is_not_reported(andt: ModuleType) -> None:
    text = "class Outer {\n  struct Inner {\n  };\n};\n"
    assert andt.definitions(text) == [("", "Outer", 1)]


def test_a_type_declared_in_a_function_body_is_not_reported(andt: ModuleType) -> None:
    text = "inline void f() {\n  struct Local {\n  };\n}\n"
    assert andt.definitions(text) == []


def test_one_name_in_two_headers_is_reported(
    andt: ModuleType, header_tree: Callable[..., Path],
) -> None:
    root = header_tree(
        **{
            "a.h": "namespace delta {\nenum class Sev {\n};\n}\n",
            "b.h": "namespace delta {\nenum class Sev {\n};\n}\n",
        },
    )
    assert sorted(
        path.name for path, _ in andt.duplicate_definitions([root])[("delta", "Sev")]
    ) == ["a.h", "b.h"]


def test_the_line_of_each_definition_is_reported(
    andt: ModuleType, header_tree: Callable[..., Path],
) -> None:
    root = header_tree(
        **{
            "a.h": "namespace delta {\nclass F {\n};\n}\n",
            "b.h": "\n\nnamespace delta {\nclass F {\n};\n}\n",
        },
    )
    assert sorted(
        line for _, line in andt.duplicate_definitions([root])[("delta", "F")]
    ) == [2, 4]


def test_one_name_in_one_header_is_not_reported(
    andt: ModuleType, header_tree: Callable[..., Path],
) -> None:
    root = header_tree(**{"a.h": "class F {\n};\n"})
    assert andt.duplicate_definitions([root]) == {}


def test_one_name_twice_in_one_header_is_not_reported(
    andt: ModuleType, header_tree: Callable[..., Path],
) -> None:
    root = header_tree(**{"a.h": "class F {\n};\nclass F {\n};\n"})
    assert andt.duplicate_definitions([root]) == {}


def test_one_name_in_two_namespaces_is_not_reported(
    andt: ModuleType, header_tree: Callable[..., Path],
) -> None:
    root = header_tree(
        **{
            "a.h": "namespace one {\nclass F {\n};\n}\n",
            "b.h": "namespace two {\nclass F {\n};\n}\n",
        },
    )
    assert andt.duplicate_definitions([root]) == {}


def test_a_definition_in_a_cpp_file_is_not_read(
    andt: ModuleType, header_tree: Callable[..., Path],
) -> None:
    root = header_tree(
        **{"a.h": "class F {\n};\n", "b.cpp": "class F {\n};\n"},
    )
    assert andt.duplicate_definitions([root]) == {}


def test_headers_are_found_below_a_subdirectory(
    andt: ModuleType, header_tree: Callable[..., Path],
) -> None:
    root = header_tree(
        **{
            "one__a.h": "class F {\n};\n",
            "two__deep__b.h": "class F {\n};\n",
        },
    )
    assert len(andt.duplicate_definitions([root])[("", "F")]) == 2


def test_a_clean_tree_exits_zero(andt: ModuleType, header_tree: Callable[..., Path]) -> None:
    assert andt.main([header_tree(**{"a.h": "class F {\n};\n"})]) == 0


def test_a_duplicate_exits_one(andt: ModuleType, header_tree: Callable[..., Path]) -> None:
    root = header_tree(
        **{"a.h": "class F {\n};\n", "b.h": "class F {\n};\n"},
    )
    assert andt.main([root]) == 1


def test_each_header_is_annotated(
    andt: ModuleType, header_tree: Callable[..., Path],
    capsys: pytest.CaptureFixture[str],
) -> None:
    report = _report_on_two_headers_defining_f(andt, header_tree, capsys)
    assert report.count("::error file=") == 2


def test_the_report_names_the_scoped_type(
    andt: ModuleType,
    header_tree: Callable[..., Path],
    capsys: pytest.CaptureFixture[str],
) -> None:
    text = "namespace delta {\nclass F {\n};\n}\n"
    root = header_tree(**{"a.h": text, "b.h": text})
    andt.main([root])
    assert "delta::F is defined by 2 headers" in capsys.readouterr().out


def test_the_report_of_a_file_scope_type_names_it_alone(
    andt: ModuleType, header_tree: Callable[..., Path],
    capsys: pytest.CaptureFixture[str],
) -> None:
    report = _report_on_two_headers_defining_f(andt, header_tree, capsys)
    assert "line=1::F is defined by 2 headers" in report


def _report_on_two_headers_defining_f(
    andt: ModuleType, header_tree: Callable[..., Path],
    capsys: pytest.CaptureFixture[str],
) -> str:
    root = header_tree(**{"a.h": "class F {\n};\n", "b.h": "class F {\n};\n"})
    andt.main([root])
    return capsys.readouterr().out


def test_running_the_module_exits_with_the_status_main_returned(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    for root in ("src", "lib", "test"):
        (tmp_path / root).mkdir()
    monkeypatch.chdir(tmp_path)
    with pytest.raises(SystemExit, match="^0$"):
        runpy.run_module("assert_no_duplicate_type_definitions")
