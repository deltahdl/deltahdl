#include <gtest/gtest.h>

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <string>

#include "fixture_preprocessor.h"

using namespace delta;

// ---------------------------------------------------------------------------
// Syntax 22-4: undefine_compiler_directive ::= `undef text_macro_identifier
//
// The claims exercised here are the ones §22.5.2 itself states:
//   C1  the directive is the keyword `undef followed by a text_macro_identifier
//   C2  it removes the named macro if a `define created it in this
//       compilation unit
//   C3  removing a macro that was never defined is permitted (a warning is
//       allowed, an error is not)
//   C4  the removed macro has no value afterwards, exactly as if it had never
//       been defined
//
// The macros the directive operates on are built with the real §22.5.1
// `define syntax: object-like bodies, blank bodies, formal argument lists and
// argument defaults, and escaped identifiers as macro names.
// ---------------------------------------------------------------------------

namespace {

// Flattens preprocessor output so two runs can be compared as a single value.
std::string Flatten(const std::string& text) {
  std::string flat;
  for (char c : text) flat += (c == '\n') ? '|' : c;
  return flat;
}

// A scratch directory for the one test that needs a second source file to put
// a `define and its `undef in different files of the same compilation unit.
struct UndefIncludeDir {
  std::filesystem::path dir;

  UndefIncludeDir() {
    dir = std::filesystem::temp_directory_path() /
          ("delta_undef_" + std::to_string(getpid()));
    std::filesystem::create_directories(dir);
  }

  ~UndefIncludeDir() { std::filesystem::remove_all(dir); }

  void WriteFile(const std::string& rel_path, const std::string& content) {
    std::ofstream ofs(dir / rel_path);
    ofs << content;
  }
};

}  // namespace

// --- C1: the text_macro_identifier operand, in each of its forms -----------

TEST(UndefPreprocessing, UndefPreviouslyDefinedMacro) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 42\n"
      "`undef FOO\n"
      "`ifdef FOO\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("visible"), std::string::npos);
}

// Syntax 22-4 accepts an escaped identifier as the `undef argument. The
// directive's name parser must take the escaped-name branch and remove the
// macro stored under that escaped key, just like a simple identifier.
TEST(UndefPreprocessing, UndefEscapedIdentifierMacro) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define \\M@CRO 7\n"
      "`undef \\M@CRO\n"
      "`ifdef \\M@CRO\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("visible"), std::string::npos);
}

// A text_macro_identifier names a macro regardless of whether `define gave it
// a formal argument list, so the operand form here is a function-like macro.
TEST(UndefPreprocessing, UndefFunctionLikeMacroName) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define SUM(a,b) (a)+(b)\n"
      "`undef SUM\n"
      "`ifdef SUM\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("visible"), std::string::npos);
}

// Same operand form, but the macro carries argument defaults. The defaults are
// stored alongside the definition and must disappear with it.
TEST(UndefPreprocessing, UndefMacroWithArgumentDefaults) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define OPT(a=5,b=7) a b\n"
      "`undef OPT\n"
      "`ifdef OPT\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("visible"), std::string::npos);
}

// A macro whose `define supplied blank macro text is still a defined macro,
// and `undef removes it like any other.
TEST(UndefPreprocessing, UndefMacroDefinedWithBlankText) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FLAG\n"
      "`undef FLAG\n"
      "`ifdef FLAG\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("visible"), std::string::npos);
}

// The operand spans a whole simple_identifier, including the digits, dollar
// signs and underscores that may follow its first character.
TEST(UndefPreprocessing, UndefNameSpansFullIdentifierCharacterSet) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define _w1$d 42\n"
      "`undef _w1$d\n"
      "`ifdef _w1$d\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("visible"), std::string::npos);
}

// A `define whose macro text is carried across physical lines by a backslash
// still produces one macro, and the operand naming it is an ordinary
// text_macro_identifier.
TEST(UndefPreprocessing, UndefRemovesMacroWithBackslashContinuedBody) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define LONG a + \\\n"
      "  b + c\n"
      "`undef LONG\n"
      "`ifdef LONG\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("visible"), std::string::npos);
}

// The other syntactic position the directive can occupy: after source text on
// the same line. The macro still goes away and the text ahead of it survives.
TEST(UndefPreprocessing, UndefFollowingSourceTextOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 42\n"
      "int x = 1; `undef FOO\n"
      "`ifdef FOO\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1;"), std::string::npos);
  EXPECT_EQ(result.find("visible"), std::string::npos);
}

// --- C1 negative: inputs the directive form must reject -------------------

// Syntax 22-4 makes the text_macro_identifier part of the directive, so a bare
// `undef is not a well-formed directive and must be diagnosed rather than
// quietly removing nothing.
TEST(UndefPreprocessing, UndefWithoutMacroNameIsAnError) {
  PreprocFixture f;
  Preprocess(
      "`define FOO 1\n"
      "`undef\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// text_macro_identifier resolves to an identifier, which §5.6 never starts
// with a digit. A digit-led operand is therefore ungrammatical rather than a
// name that merely happens not to be defined.
TEST(UndefPreprocessing, UndefWithNonIdentifierOperandIsAnError) {
  PreprocFixture f;
  Preprocess("`undef 123\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// A bare `undef inside a conditional branch that is not compiled is skipped
// along with the rest of that branch, so it raises no diagnostic.
TEST(UndefPreprocessing, UndefWithoutMacroNameInInactiveBranchIsNotAnError) {
  PreprocFixture f;
  Preprocess(
      "`ifdef NOT_DEFINED\n"
      "`undef\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// The closest rejectable input to the directive: the keyword has to be a token
// of its own. `undefX runs a name character straight into the keyword, which
// makes it a usage of the macro undefX, not `undef applied to X. The macro
// must expand and X must survive.
TEST(UndefPreprocessing, KeywordRunTogetherWithNameIsAMacroUsageNotUndef) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define X 5\n"
      "`define undefX 9\n"
      "`undefX\n"
      "`ifdef X\n"
      "survived\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find('9'), std::string::npos);
  EXPECT_NE(result.find("survived"), std::string::npos);
}

// The same run-together spelling with no such macro defined is an undefined
// macro usage, not a silent `undef of the trailing name.
TEST(UndefPreprocessing, KeywordRunTogetherWithUndefinedNameDoesNotUndefine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define X 5\n"
      "`undefX\n"
      "`ifdef X\n"
      "survived\n"
      "`endif\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_NE(result.find("survived"), std::string::npos);
}

// The keyword-boundary reading has to hold in the other position the spelling
// can occupy too. Mid-expression, `undefX is reached by a different code path
// than a line-leading one, and must likewise expand the macro rather than
// delete X.
TEST(UndefPreprocessing, KeywordRunTogetherWithNameInExpressionIsAMacroUsage) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define X 5\n"
      "`define undefX 9\n"
      "int y = `undefX;\n"
      "`ifdef X\n"
      "survived\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int y = 9;"), std::string::npos);
  EXPECT_NE(result.find("survived"), std::string::npos);
}

// --- C2: removes the named macro, and only that macro ---------------------

TEST(UndefPreprocessing, UndefDoesNotAffectOtherMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define A 1\n"
      "`define B 2\n"
      "`undef A\n"
      "int x = `B;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find('2'), std::string::npos);
}

// §22.5.1 lets a macro be redefined, with the latest definition prevailing.
// `undef removes the macro outright; it does not restore the earlier text.
TEST(UndefPreprocessing, UndefRemovesRedefinedMacroEntirely) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define V 11\n"
      "`define V 22\n"
      "`undef V\n"
      "`ifdef V\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("visible"), std::string::npos);
  EXPECT_EQ(result.find("11"), std::string::npos);
}

// After the definition is gone, a call-shaped usage no longer expands.
TEST(UndefPreprocessing, UndefStopsFunctionLikeMacroFromExpanding) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define SUM(a,b) (a)+(b)\n"
      "`undef SUM\n"
      "int z = `SUM(1,2);\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_NE(result.find("`SUM(1,2)"), std::string::npos);
}

// §22.5.1 allows `define both inside and outside a design element, so `undef
// has to reach a definition made inside a module body too.
TEST(UndefPreprocessing, UndefRemovesMacroDefinedInsideDesignElement) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "`define W 4\n"
      "`undef W\n"
      "`ifdef W\n"
      "visible\n"
      "`endif\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("visible"), std::string::npos);
}

// The reach of `undef is the compilation unit, not the file: a macro that an
// included file defined is removable from the file that included it.
TEST(UndefPreprocessing, UndefRemovesMacroDefinedInAnIncludedFile) {
  UndefIncludeDir tmp;
  tmp.WriteFile("defs.svh", "`define FROM_INCLUDE 42\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile(tmp.dir / "top.sv",
                           "`include \"defs.svh\"\n"
                           "`undef FROM_INCLUDE\n"
                           "`ifdef FROM_INCLUDE\n"
                           "visible\n"
                           "`endif\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("visible"), std::string::npos);
}

// The positive half of the conditional pairing: sitting inside a branch that
// is compiled is another position the directive can occupy, and there it does
// perform the removal.
TEST(UndefPreprocessing, UndefInsideCompiledConditionalBranchRemovesMacro) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define GATE\n"
      "`define TARGET 42\n"
      "`ifdef GATE\n"
      "`undef TARGET\n"
      "`endif\n"
      "`ifdef TARGET\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("visible"), std::string::npos);
  EXPECT_EQ(result.find("42"), std::string::npos);
}

// The removal happens only where the directive is actually compiled.
TEST(UndefPreprocessing, UndefInInactiveConditionalSkipped) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define KEEP 42\n"
      "`ifdef UNDEF_MACRO\n"
      "`undef KEEP\n"
      "`endif\n"
      "int x = `KEEP;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("42"), std::string::npos);
}

// --- C3: undefining something never defined is allowed --------------------

TEST(UndefPreprocessing, UndefOfNeverDefinedMacroIsNotAnError) {
  PreprocFixture f;
  Preprocess("`undef NEVER_DEFINED\n", f);

  EXPECT_FALSE(f.diag.HasErrors());
}

// The report §22.5.2 allows for that case, and the ceiling it sets on it: a
// warning is raised, and it stays a warning rather than becoming an error.
TEST(UndefPreprocessing, UndefOfNeverDefinedMacroWarns) {
  PreprocFixture f;
  Preprocess("`undef NEVER_DEFINED\n", f);

  EXPECT_EQ(f.diag.WarningCount(), 1u);
  EXPECT_FALSE(f.diag.HasErrors());
}

// The other side of the same rule: removing a macro that a `define really did
// create is the ordinary case and must stay silent.
TEST(UndefPreprocessing, UndefOfDefinedMacroDoesNotWarn) {
  PreprocFixture f;
  Preprocess(
      "`define FOO 42\n"
      "`undef FOO\n",
      f);

  EXPECT_EQ(f.diag.WarningCount(), 0u);
  EXPECT_FALSE(f.diag.HasErrors());
}

// A second removal of the same name is the never-defined case, since the first
// one already took the definition away.
TEST(UndefPreprocessing, SecondUndefOfSameNameWarns) {
  PreprocFixture f;
  Preprocess(
      "`define FOO 1\n"
      "`undef FOO\n"
      "`undef FOO\n",
      f);

  EXPECT_EQ(f.diag.WarningCount(), 1u);
  EXPECT_FALSE(f.diag.HasErrors());
}

// A directive inside a branch that is not compiled performs no attempt at all,
// so it has nothing to report.
TEST(UndefPreprocessing, UndefInInactiveBranchDoesNotWarn) {
  PreprocFixture f;
  Preprocess(
      "`ifdef NOT_DEFINED\n"
      "`undef NEVER_DEFINED\n"
      "`endif\n",
      f);

  EXPECT_EQ(f.diag.WarningCount(), 0u);
  EXPECT_FALSE(f.diag.HasErrors());
}

// The second `undef of the same name is that same permitted case, since the
// first one already removed the definition.
TEST(UndefPreprocessing, UndefTwiceIsNotAnError) {
  PreprocFixture f;
  Preprocess(
      "`define FOO 1\n"
      "`undef FOO\n"
      "`undef FOO\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- C4: afterwards the macro has no value, as if never defined -----------

TEST(UndefPreprocessing, UndefinedMacroHasNoValue) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 42\n"
      "`undef FOO\n"
      "int x = `FOO;\n",
      f);

  EXPECT_NE(result.find("`FOO"), std::string::npos);
  EXPECT_EQ(result.find("42"), std::string::npos);
}

// "As if it had never been defined" is an equivalence, so the removed name has
// to behave exactly like a name the source never mentioned: same emitted text
// and the same diagnostic outcome.
TEST(UndefPreprocessing, RemovedMacroBehavesExactlyLikeNeverDefinedMacro) {
  PreprocFixture undefd;
  auto after_undef = Preprocess(
      "`define NAME 3\n"
      "`undef NAME\n"
      "int z = `NAME;\n",
      undefd);

  PreprocFixture never;
  auto never_defined = Preprocess("int z = `NAME;\n", never);

  EXPECT_EQ(undefd.diag.HasErrors(), never.diag.HasErrors());
  // The `define/`undef pair leaves two blank lines ahead of the usage; the
  // surviving text must otherwise match the never-defined run character for
  // character.
  EXPECT_EQ(Flatten(after_undef), "||" + Flatten(never_defined));
}

// A removed macro leaves nothing behind for `ifndef either.
TEST(UndefPreprocessing, UndefMakesIfndefBranchCompile) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FEATURE\n"
      "`undef FEATURE\n"
      "`ifndef FEATURE\n"
      "reached\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("reached"), std::string::npos);
}

TEST(UndefPreprocessing, UndefThenRedefineUsesNewMacroText) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define VAL 1\n"
      "`undef VAL\n"
      "`define VAL 2\n"
      "int x = `VAL;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find('2'), std::string::npos);
}

// Redefining after the removal starts from nothing, so the formal argument
// list of the old definition cannot linger: the new object-like macro expands
// without consuming a following parenthesized list.
TEST(UndefPreprocessing, RedefineAfterUndefLeavesNoFormalArgumentResidue) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M(a,b) (a)+(b)\n"
      "`undef M\n"
      "`define M 5\n"
      "int z = `M;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int z = 5;"), std::string::npos);
}
