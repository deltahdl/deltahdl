#include <gtest/gtest.h>
#include <unistd.h>

#include <filesystem>
#include <fstream>
#include <string>

#include "fixture_preprocessor.h"
#include "preprocessor/preprocessor.h"

using namespace delta;
namespace fs = std::filesystem;

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
  EXPECT_EQ(result.find("after 8"), std::string::npos);
  EXPECT_NE(result.find("after 64"), std::string::npos);
  EXPECT_EQ(result.find("witness_survived"), std::string::npos);
}

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
  EXPECT_EQ(result.find("foo_visible"), std::string::npos);
  EXPECT_EQ(result.find("bar_visible"), std::string::npos);
  EXPECT_NE(result.find("FOO"), std::string::npos);
}

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
  EXPECT_NE(result.find("// a note about the wipe\n"), std::string::npos);
  EXPECT_EQ(result.find("foo_visible"), std::string::npos);
}

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
