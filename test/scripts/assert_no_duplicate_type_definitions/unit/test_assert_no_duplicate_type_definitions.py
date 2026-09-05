"""Unit tests for assert_no_duplicate_type_definitions."""

from collections.abc import Callable
from pathlib import Path
from types import ModuleType

import pytest


class TestStripCommentsAndStrings:
    """Tests for strip_comments_and_strings()."""

    def test_a_line_comment_is_blanked(self, andt: ModuleType) -> None:
        """A // comment should leave nothing that reads as code."""
        assert "class" not in andt.strip_comments_and_strings("int x;  // class C {\n")

    def test_a_block_comment_is_blanked(self, andt: ModuleType) -> None:
        """A /* */ comment should leave nothing that reads as code."""
        assert "struct" not in andt.strip_comments_and_strings("/* struct S { */ int x;")

    def test_a_block_comment_keeps_its_newlines(self, andt: ModuleType) -> None:
        """A multi-line comment should not move the lines after it.

        The line a definition stands on is what this module reports, so a
        stripper that collapsed a comment would report every later definition
        at the wrong line.
        """
        stripped = andt.strip_comments_and_strings("/* a\nb\nc */\nclass C {\n")
        assert stripped.splitlines()[3].strip() == "class C {"

    def test_a_string_literal_is_blanked(self, andt: ModuleType) -> None:
        """A brace inside a literal should not be counted as a brace.

        An unbalanced brace throws the depth count off for the rest of the
        file, which puts every later definition at the wrong scope.
        """
        assert "{" not in andt.strip_comments_and_strings('const char* s = "{";')

    def test_an_escaped_quote_does_not_end_a_literal(self, andt: ModuleType) -> None:
        """A \\" inside a literal should leave the literal open."""
        assert "{" not in andt.strip_comments_and_strings('const char* s = "a\\"{";')

    def test_an_unterminated_block_comment_reaches_the_end(
        self, andt: ModuleType,
    ) -> None:
        """A /* with no */ should blank the rest of the text rather than raise."""
        assert andt.strip_comments_and_strings("int x; /* class C {").strip() == "int x;"

    def test_an_unterminated_literal_reaches_the_end(self, andt: ModuleType) -> None:
        """A quote with no closing quote should blank the rest rather than raise."""
        assert "{" not in andt.strip_comments_and_strings('const char* s = "{')

    def test_code_either_side_of_a_comment_is_not_joined(
        self, andt: ModuleType,
    ) -> None:
        """Removing a comment should not make one token of its two neighbours."""
        assert andt.strip_comments_and_strings("a/*x*/b") == "a     b"


class TestDefinitions:
    """Tests for definitions()."""

    def test_a_class_definition_is_found(self, andt: ModuleType) -> None:
        """A class with a body should be reported under its name."""
        assert andt.definitions("class Frame {\n};\n") == [("", "Frame", 1)]

    def test_a_struct_definition_is_found(self, andt: ModuleType) -> None:
        """A struct with a body should be reported under its name."""
        assert andt.definitions("struct Pair {\n};\n") == [("", "Pair", 1)]

    def test_a_union_definition_is_found(self, andt: ModuleType) -> None:
        """A union with a body should be reported under its name."""
        assert andt.definitions("union Slot {\n};\n") == [("", "Slot", 1)]

    def test_an_enum_class_definition_is_found(self, andt: ModuleType) -> None:
        """An enum class should be reported under its name and not under class.

        `enum class` is the shape the recorded collision had, and a pattern
        stopping at the first keyword would read `class` as the name.
        """
        assert andt.definitions("enum class Severity : uint8_t {\n};\n") == [
            ("", "Severity", 1),
        ]

    def test_a_plain_enum_definition_is_found(self, andt: ModuleType) -> None:
        """An unscoped enum should be reported under its name."""
        assert andt.definitions("enum Colour {\n};\n") == [("", "Colour", 1)]

    def test_a_forward_declaration_is_not_a_definition(
        self, andt: ModuleType,
    ) -> None:
        """`class Frame;` declares and does not define.

        A forward declaration may stand in any number of headers, which is
        what it is for.
        """
        assert andt.definitions("class Frame;\n") == []

    def test_a_variable_of_a_struct_type_is_not_a_definition(
        self, andt: ModuleType,
    ) -> None:
        """`struct Frame f;` names a type rather than defining one."""
        assert andt.definitions("struct Frame frame;\n") == []

    def test_a_base_clause_may_put_the_brace_on_a_later_line(
        self, andt: ModuleType,
    ) -> None:
        """A definition whose brace follows its head should still be found."""
        assert andt.definitions("class Frame\n    : public Base {\n};\n") == [
            ("", "Frame", 1),
        ]

    def test_a_head_with_no_brace_or_semicolon_is_not_a_definition(
        self, andt: ModuleType,
    ) -> None:
        """A head running to the end of the file should be reported as neither."""
        assert andt.definitions("class Frame\n") == []

    def test_a_template_specialization_is_not_a_definition(
        self, andt: ModuleType,
    ) -> None:
        """`struct Traits<int>` specializes rather than defining a new name.

        Reading it as a definition would report the primary template and its
        specialization as two definitions of one name.
        """
        assert andt.definitions("template <>\nstruct Traits<int> {\n};\n") == []

    def test_a_template_definition_is_found(self, andt: ModuleType) -> None:
        """A primary template written on one line should be reported."""
        assert andt.definitions("template <typename T> struct Traits {\n};\n") == [
            ("", "Traits", 1),
        ]

    def test_the_namespace_is_recorded(self, andt: ModuleType) -> None:
        """A definition should carry the namespace it stands in."""
        assert andt.definitions("namespace delta {\nclass Frame {\n};\n}\n") == [
            ("delta", "Frame", 2),
        ]

    def test_a_nested_namespace_is_joined(self, andt: ModuleType) -> None:
        """`namespace a::b {` should record both components."""
        assert andt.definitions("namespace a::b {\nclass F {\n};\n}\n") == [
            ("a::b", "F", 2),
        ]

    def test_two_namespace_lines_are_joined(self, andt: ModuleType) -> None:
        """Two nested namespaces should record as one path."""
        text = "namespace a {\nnamespace b {\nclass F {\n};\n}\n}\n"
        assert andt.definitions(text) == [("a::b", "F", 3)]

    def test_an_anonymous_namespace_is_named(self, andt: ModuleType) -> None:
        """`namespace {` should record a path rather than none."""
        assert andt.definitions("namespace {\nclass F {\n};\n}\n") == [
            ("(anonymous)", "F", 2),
        ]

    def test_a_definition_after_a_namespace_closes_is_at_the_outer_scope(
        self, andt: ModuleType,
    ) -> None:
        """A closing brace should take the namespace back off the path."""
        text = "namespace a {\n}\nclass F {\n};\n"
        assert andt.definitions(text) == [("", "F", 3)]

    def test_a_type_nested_in_a_class_is_not_reported(
        self, andt: ModuleType,
    ) -> None:
        """A class member type is named by its enclosing class.

        So it cannot collide with a type of the same name nested in another,
        and only the enclosing class is this module's business.
        """
        text = "class Outer {\n  struct Inner {\n  };\n};\n"
        assert andt.definitions(text) == [("", "Outer", 1)]

    def test_a_type_declared_in_a_function_body_is_not_reported(
        self, andt: ModuleType,
    ) -> None:
        """A type local to a function is visible to no other translation unit."""
        text = "inline void f() {\n  struct Local {\n  };\n}\n"
        assert andt.definitions(text) == []


class TestDuplicateDefinitions:
    """Tests for duplicate_definitions()."""

    def test_one_name_in_two_headers_is_reported(
        self, andt: ModuleType, header_tree: Callable[..., Path],
    ) -> None:
        """Two headers defining one scoped name should be reported together."""
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
        self, andt: ModuleType, header_tree: Callable[..., Path],
    ) -> None:
        """A report should carry where in each header the definition stands."""
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
        self, andt: ModuleType, header_tree: Callable[..., Path],
    ) -> None:
        """A name defined once should not be reported."""
        root = header_tree(**{"a.h": "class F {\n};\n"})
        assert andt.duplicate_definitions([root]) == {}

    def test_one_name_twice_in_one_header_is_not_reported(
        self, andt: ModuleType, header_tree: Callable[..., Path],
    ) -> None:
        """Two definitions in one header are what an #if/#else pair looks like.

        The compiler takes one of them, so the header holds one definition and
        this is not the collision being reported.
        """
        root = header_tree(**{"a.h": "class F {\n};\nclass F {\n};\n"})
        assert andt.duplicate_definitions([root]) == {}

    def test_one_name_in_two_namespaces_is_not_reported(
        self, andt: ModuleType, header_tree: Callable[..., Path],
    ) -> None:
        """Two namespaces holding one name hold two types, which is legal."""
        root = header_tree(
            **{
                "a.h": "namespace one {\nclass F {\n};\n}\n",
                "b.h": "namespace two {\nclass F {\n};\n}\n",
            },
        )
        assert andt.duplicate_definitions([root]) == {}

    def test_a_definition_in_a_cpp_file_is_not_read(
        self, andt: ModuleType, header_tree: Callable[..., Path],
    ) -> None:
        """A .cpp file's definition is visible to that file alone.

        Two of them are not a collision, and an #include reaches a header.
        """
        root = header_tree(
            **{"a.h": "class F {\n};\n", "b.cpp": "class F {\n};\n"},
        )
        assert andt.duplicate_definitions([root]) == {}

    def test_headers_are_found_below_a_subdirectory(
        self, andt: ModuleType, header_tree: Callable[..., Path],
    ) -> None:
        """A root should be searched to its leaves and not one level down."""
        root = header_tree(
            **{
                "one__a.h": "class F {\n};\n",
                "two__deep__b.h": "class F {\n};\n",
            },
        )
        assert len(andt.duplicate_definitions([root])[("", "F")]) == 2


class TestMain:
    """Tests for main()."""

    def test_a_clean_tree_exits_zero(
        self, andt: ModuleType, header_tree: Callable[..., Path],
    ) -> None:
        """A tree with no duplicate should report success."""
        assert andt.main([header_tree(**{"a.h": "class F {\n};\n"})]) == 0

    def test_a_duplicate_exits_one(
        self, andt: ModuleType, header_tree: Callable[..., Path],
    ) -> None:
        """A tree with a duplicate should report failure."""
        root = header_tree(
            **{"a.h": "class F {\n};\n", "b.h": "class F {\n};\n"},
        )
        assert andt.main([root]) == 1

    def test_each_header_is_annotated(
        self,
        andt: ModuleType,
        header_tree: Callable[..., Path],
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        """Both headers should carry an annotation, neither being the one to fix."""
        root = header_tree(
            **{"a.h": "class F {\n};\n", "b.h": "class F {\n};\n"},
        )
        andt.main([root])
        assert capsys.readouterr().out.count("::error file=") == 2

    def test_the_report_names_the_scoped_type(
        self,
        andt: ModuleType,
        header_tree: Callable[..., Path],
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A namespaced name should be reported with its namespace.

        Two types of one name in different namespaces are different types, so
        a report naming the bare name would not say which one was found twice.
        """
        text = "namespace delta {\nclass F {\n};\n}\n"
        root = header_tree(**{"a.h": text, "b.h": text})
        andt.main([root])
        assert "delta::F is defined by 2 headers" in capsys.readouterr().out

    def test_the_report_of_a_file_scope_type_names_it_alone(
        self,
        andt: ModuleType,
        header_tree: Callable[..., Path],
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A type in no namespace should be named without a leading `::`.

        The message is pinned to the annotation prefix it follows, because the
        prefix itself ends in `::` and a search for `::F` would find that.
        """
        root = header_tree(
            **{"a.h": "class F {\n};\n", "b.h": "class F {\n};\n"},
        )
        andt.main([root])
        assert "line=1::F is defined by 2 headers" in capsys.readouterr().out
