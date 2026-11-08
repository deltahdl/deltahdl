#include <gtest/gtest.h>
#include <unistd.h>

#include <filesystem>
#include <fstream>
#include <string>

#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

std::string Flatten(const std::string& text) {
  std::string flat;
  for (char c : text) flat += (c == '\n') ? '|' : c;
  return flat;
}

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

TEST(UndefPreprocessing, UndefEscapedIdentifierFollowedByText) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define \\M@CRO 7\n"
      "`undef \\M@CRO wire w;\n"
      "`ifdef \\M@CRO\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("wire w;"), std::string::npos);
  EXPECT_EQ(result.find("visible"), std::string::npos);
}

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

TEST(UndefPreprocessing, UndefWithoutMacroNameIsAnError) {
  PreprocFixture f;
  Preprocess(
      "`define FOO 1\n"
      "`undef\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`undef requires a text macro name", 2, "22.5.2"));
}

TEST(UndefPreprocessing, UndefWithNonIdentifierOperandIsAnError) {
  PreprocFixture f;
  Preprocess("`undef 123\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`undef requires a text macro name", 1, "22.5.2"));
}

TEST(UndefPreprocessing, UndefWithoutMacroNameInInactiveBranchIsNotAnError) {
  PreprocFixture f;
  Preprocess(
      "`ifdef NOT_DEFINED\n"
      "`undef\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

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

TEST(UndefPreprocessing, KeywordRunTogetherWithUndefinedNameDoesNotUndefine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define X 5\n"
      "`undefX\n"
      "`ifdef X\n"
      "survived\n"
      "`endif\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undefined macro 'undefX'", 2,
                            "22.5.1"));
  EXPECT_NE(result.find("survived"), std::string::npos);
}

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

TEST(UndefPreprocessing, UndefStopsFunctionLikeMacroFromExpanding) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define SUM(a,b) (a)+(b)\n"
      "`undef SUM\n"
      "int z = `SUM(1,2);\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undefined macro 'SUM'", 3,
                            "22.5.1"));
  EXPECT_NE(result.find("`SUM(1,2)"), std::string::npos);
}

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

TEST(UndefPreprocessing, UndefOfNeverDefinedMacroIsNotAnError) {
  PreprocFixture f;
  Preprocess("`undef NEVER_DEFINED\n", f);

  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UndefPreprocessing, UndefOfNeverDefinedMacroWarns) {
  PreprocFixture f;
  Preprocess("`undef NEVER_DEFINED\n", f);

  EXPECT_EQ(f.diag.WarningCount(), 1u);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UndefPreprocessing, UndefOfDefinedMacroDoesNotWarn) {
  PreprocFixture f;
  Preprocess(
      "`define FOO 42\n"
      "`undef FOO\n",
      f);

  EXPECT_EQ(f.diag.WarningCount(), 0u);
  EXPECT_FALSE(f.diag.HasErrors());
}

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

TEST(UndefPreprocessing, UndefTwiceIsNotAnError) {
  PreprocFixture f;
  Preprocess(
      "`define FOO 1\n"
      "`undef FOO\n"
      "`undef FOO\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UndefPreprocessing, UndefinedMacroHasNoValue) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 42\n"
      "`undef FOO\n"
      "int x = `FOO;\n",
      f);

  EXPECT_NE(result.find("`FOO"), std::string::npos);
  EXPECT_EQ(result.find("42"), std::string::npos);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undefined macro 'FOO'", 3,
                            "22.5.1"));
}

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
  EXPECT_EQ(Flatten(after_undef), "||" + Flatten(never_defined));
}

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
