#include <gtest/gtest.h>

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <string>

#include "fixture_preprocessor.h"

using namespace delta;
namespace fs = std::filesystem;

// A compilation unit is not a single file, so the reach of `undefineall has to
// be checked across an `include boundary. This writes the extra files the
// multi-file cases need.
struct UndefineAllUnitDir {
  fs::path dir;

  UndefineAllUnitDir() {
    dir = fs::temp_directory_path() /
          ("delta_undefineall_" + std::to_string(getpid()));
    fs::create_directories(dir);
  }

  ~UndefineAllUnitDir() { fs::remove_all(dir); }

  void WriteFile(const std::string& rel_path, const std::string& content) {
    auto full = dir / rel_path;
    fs::create_directories(full.parent_path());
    std::ofstream ofs(full);
    ofs << content;
  }
};

// §22.5.3 `undefineall. Three requirements live in this subclause:
//   C1  the directive removes every text macro `define created earlier in the
//       compilation unit,
//   C2  it takes no arguments,
//   C3  it may appear anywhere in the source description.
// The macros it operates on are built with the real `define syntax of §22.5.1
// (object-like, function-like, defaulted arguments, escaped names, empty and
// continued bodies), and removal is observed through `ifdef and through a
// macro usage that would otherwise expand.

// ---------------------------------------------------------------------------
// C1: every previously defined macro is removed.
// ---------------------------------------------------------------------------

// The claim reaches every macro at once and names no macro shape, so each form
// §22.5.1 can define has to go: object-like, function-like, function-like with
// argument defaults, an escaped-identifier name, an empty body, and a
// backslash-continued body.
TEST(UndefineAllPreprocessing, UndefineAllRemovesEveryMacroForm) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define OBJ 1\n"
      "`define FUNC(a) a\n"
      "`define DEFAULTED(a = 5, b = 6) a\n"
      "`define \\ESC@NAME 1\n"
      "`define EMPTY\n"
      "`define CONTINUED first \\\n"
      "  second\n"
      "`undefineall\n"
      "`ifdef OBJ\n"
      "obj_visible\n"
      "`endif\n"
      "`ifdef FUNC\n"
      "func_visible\n"
      "`endif\n"
      "`ifdef DEFAULTED\n"
      "defaulted_visible\n"
      "`endif\n"
      "`ifdef \\ESC@NAME\n"
      "esc_visible\n"
      "`endif\n"
      "`ifdef EMPTY\n"
      "empty_visible\n"
      "`endif\n"
      "`ifdef CONTINUED\n"
      "continued_visible\n"
      "`endif\n",
      f);
  EXPECT_EQ(result.find("obj_visible"), std::string::npos);
  EXPECT_EQ(result.find("func_visible"), std::string::npos);
  EXPECT_EQ(result.find("defaulted_visible"), std::string::npos);
  EXPECT_EQ(result.find("esc_visible"), std::string::npos);
  EXPECT_EQ(result.find("empty_visible"), std::string::npos);
  EXPECT_EQ(result.find("continued_visible"), std::string::npos);
}

// Removal is observable at the point of use, not just through `ifdef: a body
// that would have been substituted before the directive no longer is after it.
TEST(UndefineAllPreprocessing, UndefineAllStopsLaterExpansion) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define WORDSIZE 8\n"
      "`define WITNESS\n"
      "before `WORDSIZE\n"
      "`undefineall\n"
      "`define WORDSIZE 64\n"
      "after `WORDSIZE\n"
      "`ifdef WITNESS\n"
      "witness_survived\n"
      "`endif\n",
      f);
  EXPECT_NE(result.find("before 8"), std::string::npos);
  // The old body is gone rather than lingering behind the new definition.
  EXPECT_EQ(result.find("after 8"), std::string::npos);
  EXPECT_NE(result.find("after 64"), std::string::npos);
  // WITNESS is never redefined, so this is what shows a removal happened at
  // all — the WORDSIZE half alone would read the same if it had not.
  EXPECT_EQ(result.find("witness_survived"), std::string::npos);
}

// Repeating the define/remove cycle leaves nothing behind from any earlier
// round — the directive is not a one-shot.
TEST(UndefineAllPreprocessing, RepeatedDefineUndefineAllCyclesLeaveNothing) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ROUND_ONE 1\n"
      "`undefineall\n"
      "`define ROUND_TWO 2\n"
      "`undefineall\n"
      "`ifdef ROUND_ONE\n"
      "one_visible\n"
      "`endif\n"
      "`ifdef ROUND_TWO\n"
      "two_visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("one_visible"), std::string::npos);
  EXPECT_EQ(result.find("two_visible"), std::string::npos);
}

// The compilation unit spans every file pulled in by `include, so a macro that
// an included file defined is removed by a directive in the including file.
TEST(UndefineAllPreprocessing, UndefineAllRemovesMacroDefinedInIncludedFile) {
  UndefineAllUnitDir tmp;
  tmp.WriteFile("defs.svh", "`define FROM_INCLUDE 1\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile(tmp.dir / "top.sv",
                           "`include \"defs.svh\"\n"
                           "`ifdef FROM_INCLUDE\n"
                           "before_visible\n"
                           "`endif\n"
                           "`undefineall\n"
                           "`ifdef FROM_INCLUDE\n"
                           "after_visible\n"
                           "`endif\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("before_visible"), std::string::npos);
  EXPECT_EQ(result.find("after_visible"), std::string::npos);
}

// And the reach runs the other way: the directive sitting in an included file
// removes a macro the including file defined ahead of the `include.
TEST(UndefineAllPreprocessing, UndefineAllInsideIncludedFileRemovesOuterMacro) {
  UndefineAllUnitDir tmp;
  tmp.WriteFile("wipe.svh", "`undefineall\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile(tmp.dir / "top.sv",
                           "`define FROM_OUTER 1\n"
                           "`include \"wipe.svh\"\n"
                           "`ifdef FROM_OUTER\n"
                           "outer_visible\n"
                           "`endif\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("outer_visible"), std::string::npos);
}

// With nothing defined there is simply nothing to remove; the directive is not
// an error and a repeat run is equally harmless.
TEST(UndefineAllPreprocessing, UndefineAllWithNoMacrosDefinedIsNotAnError) {
  PreprocFixture f;
  auto result = Preprocess(
      "`undefineall\n"
      "`undefineall\n"
      "int x = 5;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 5;"), std::string::npos);
}

// NEGATIVE for C1. Text a conditional excluded is not part of the compilation
// unit, so a `undefineall sitting in the dead branch removes nothing.
TEST(UndefineAllPreprocessing, UndefineAllInFalseBranchDoesNotRemoveMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define KEEP 1\n"
      "`ifdef NEVER_DEFINED\n"
      "`undefineall\n"
      "`endif\n"
      "`ifdef KEEP\n"
      "keep_visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("keep_visible"), std::string::npos);
}

// The same holds for the `else arm that a taken `ifdef compiles away.
TEST(UndefineAllPreprocessing,
     UndefineAllInUntakenElseBranchDoesNotRemoveMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define KEEP 7\n"
      "`ifdef KEEP\n"
      "taken_visible\n"
      "`else\n"
      "`undefineall\n"
      "`endif\n"
      "int x = `KEEP;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("taken_visible"), std::string::npos);
  EXPECT_NE(result.find("int x = 7;"), std::string::npos);
}

// NEGATIVE for C1, directive identity. `undefineall is a whole keyword: a name
// character against it makes the run a longer macro name, which is a macro
// usage and leaves the table alone.
TEST(UndefineAllPreprocessing,
     LongerNameStartingWithUndefineallIsNotTheDirective) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define KEEP 4\n"
      "`define undefineall_saved 11\n"
      "`undefineall_saved\n"
      "`ifdef KEEP\n"
      "keep_visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("11"), std::string::npos);
  EXPECT_NE(result.find("keep_visible"), std::string::npos);
}

// ---------------------------------------------------------------------------
// C2: the directive takes no arguments.
// ---------------------------------------------------------------------------

// Because the directive accepts no arguments, anything following it on the
// same line is not parsed as an argument: it is emitted unchanged as ordinary
// source text and raises no diagnostic. The removal still happens in full.
TEST(UndefineAllPreprocessing, UndefineAllPassesTrailingSameLineTextThrough) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 1\n"
      "`undefineall trailing_source_token\n"
      "`ifdef FOO\n"
      "foo_visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("trailing_source_token"), std::string::npos);
  EXPECT_EQ(result.find("foo_visible"), std::string::npos);
}

// NEGATIVE for C2, and the sharp line between this directive and `undef. A
// name on the line is not an operand naming the one macro to remove: every
// macro goes, and the name is left behind as plain source text.
TEST(UndefineAllPreprocessing, UndefineAllWithTrailingNameIsNotAnUndefOperand) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 1\n"
      "`define BAR 2\n"
      "`undefineall FOO\n"
      "`ifdef FOO\n"
      "foo_visible\n"
      "`endif\n"
      "`ifdef BAR\n"
      "bar_visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // `undef FOO would have spared BAR; this directive does not.
  EXPECT_EQ(result.find("foo_visible"), std::string::npos);
  EXPECT_EQ(result.find("bar_visible"), std::string::npos);
  EXPECT_NE(result.find("FOO"), std::string::npos);
}

// NEGATIVE for C2. A parenthesized list is not an argument list either — it is
// still just source text, and the macros are still removed.
TEST(UndefineAllPreprocessing, UndefineAllDoesNotConsumeParenthesizedList) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 1\n"
      "`undefineall (kept_text)\n"
      "`ifdef FOO\n"
      "foo_visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("(kept_text)"), std::string::npos);
  EXPECT_EQ(result.find("foo_visible"), std::string::npos);
}

// A comment is the third thing that can share the line. With no argument to
// take, the directive leaves it to ordinary comment handling — it is stripped
// rather than mistaken for an operand, and the removal still happens.
TEST(UndefineAllPreprocessing, UndefineAllFollowedByCommentOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 1\n"
      "`undefineall // a note about the wipe\n"
      "`ifdef FOO\n"
      "foo_visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("a note about the wipe"), std::string::npos);
  EXPECT_EQ(result.find("foo_visible"), std::string::npos);
}

// A dead-branch `undefineall must also stay silent in the output; the text
// after it belongs to the excluded region.
TEST(UndefineAllPreprocessing, UndefineAllInFalseBranchEmitsNothing) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef NEVER_DEFINED\n"
      "`undefineall excluded_source_token\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("excluded_source_token"), std::string::npos);
}

// ---------------------------------------------------------------------------
// C3: it may appear anywhere in the source description.
// ---------------------------------------------------------------------------

// Unlike the directives that are confined to the space between design
// elements, this one takes effect inside a module body.
TEST(UndefineAllPreprocessing, UndefineAllInsideDesignElementRemovesMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 1\n"
      "module m;\n"
      "`undefineall\n"
      "`ifdef FOO\n"
      "  wire foo_visible;\n"
      "`endif\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("foo_visible"), std::string::npos);
}

// Leading white space before the backtick still leaves it a directive.
TEST(UndefineAllPreprocessing, UndefineAllIndentedIsStillTheDirective) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 1\n"
      "    `undefineall\n"
      "`ifdef FOO\n"
      "foo_visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("foo_visible"), std::string::npos);
}

// Some directives are confined to the space between design elements and are
// rejected inside one. This is not among them, in a package body or an
// interface body any more than in a module body.
TEST(UndefineAllPreprocessing,
     UndefineAllInsidePackageAndInterfaceRemovesMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 1\n"
      "package p;\n"
      "`undefineall\n"
      "endpackage\n"
      "`define BAR 2\n"
      "interface i;\n"
      "`undefineall\n"
      "endinterface\n"
      "`ifdef FOO\n"
      "foo_visible\n"
      "`endif\n"
      "`ifdef BAR\n"
      "bar_visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("foo_visible"), std::string::npos);
  EXPECT_EQ(result.find("bar_visible"), std::string::npos);
}

// The remaining design element kinds the language defines are legal places for
// it too, not just the module/package/interface trio.
TEST(UndefineAllPreprocessing,
     UndefineAllInsideRemainingDesignElementKindsRemovesMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define IN_PROGRAM 1\n"
      "program p;\n"
      "`undefineall\n"
      "endprogram\n"
      "`define IN_CHECKER 1\n"
      "checker c;\n"
      "`undefineall\n"
      "endchecker\n"
      "`define IN_PRIMITIVE 1\n"
      "primitive u (o, i);\n"
      "`undefineall\n"
      "endprimitive\n"
      "`define IN_CONFIG 1\n"
      "config cfg;\n"
      "`undefineall\n"
      "endconfig\n"
      "`define IN_MACROMODULE 1\n"
      "macromodule mm;\n"
      "`undefineall\n"
      "endmodule\n"
      "`ifdef IN_PROGRAM\n"
      "program_visible\n"
      "`endif\n"
      "`ifdef IN_CHECKER\n"
      "checker_visible\n"
      "`endif\n"
      "`ifdef IN_PRIMITIVE\n"
      "primitive_visible\n"
      "`endif\n"
      "`ifdef IN_CONFIG\n"
      "config_visible\n"
      "`endif\n"
      "`ifdef IN_MACROMODULE\n"
      "macromodule_visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("program_visible"), std::string::npos);
  EXPECT_EQ(result.find("checker_visible"), std::string::npos);
  EXPECT_EQ(result.find("primitive_visible"), std::string::npos);
  EXPECT_EQ(result.find("config_visible"), std::string::npos);
  EXPECT_EQ(result.find("macromodule_visible"), std::string::npos);
}

// The gap between two design elements is a distinct position from inside one:
// the tracker has come back down to top level by then.
TEST(UndefineAllPreprocessing,
     UndefineAllBetweenTwoDesignElementsRemovesMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 1\n"
      "module a;\n"
      "endmodule\n"
      "`undefineall\n"
      "module b;\n"
      "`ifdef FOO\n"
      "  wire foo_visible;\n"
      "`endif\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("foo_visible"), std::string::npos);
}

// Deep inside a procedural block is still a legal place for it.
TEST(UndefineAllPreprocessing, UndefineAllInsideProceduralBlockRemovesMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 1\n"
      "module m;\n"
      "  initial begin\n"
      "`undefineall\n"
      "  end\n"
      "endmodule\n"
      "`ifdef FOO\n"
      "foo_visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("foo_visible"), std::string::npos);
}

// The last line of the file, with no newline closing it, is still the
// directive and still takes effect.
TEST(UndefineAllPreprocessing, UndefineAllAsFinalLineWithoutNewline) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 1\n"
      "`ifdef FOO\n"
      "foo_visible\n"
      "`endif\n"
      "`undefineall",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("foo_visible"), std::string::npos);
}

// The very first line of a file is a legal place for it, with nothing before
// it to undefine.
TEST(UndefineAllPreprocessing, UndefineAllAtStartOfFile) {
  PreprocFixture f;
  auto result = Preprocess(
      "`undefineall\n"
      "`define FOO 3\n"
      "int x = `FOO;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 3;"), std::string::npos);
}
