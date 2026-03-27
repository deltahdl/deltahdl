#include <gtest/gtest.h>

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <string>

#include "fixture_preprocessor.h"

using namespace delta;
namespace fs = std::filesystem;

struct IncludeTestDir {
  fs::path dir;

  IncludeTestDir() {
    dir =
        fs::temp_directory_path() / ("delta_test_" + std::to_string(getpid()));
    fs::create_directories(dir);
  }

  ~IncludeTestDir() { fs::remove_all(dir); }

  fs::path WriteFile(const std::string& rel_path, const std::string& content) {
    auto full = dir / rel_path;
    fs::create_directories(full.parent_path());
    std::ofstream ofs(full);
    ofs << content;
    return full;
  }
};

TEST(Preprocessor, DefineRecognized) {
  PreprocFixture f;
  Preprocess("`define MY_MACRO 1\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, UndefRecognized) {
  PreprocFixture f;
  Preprocess("`define FOO 1\n`undef FOO\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, UndefineallRecognized) {
  PreprocFixture f;
  Preprocess("`undefineall\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, IfdefRecognized) {
  PreprocFixture f;
  Preprocess("`ifdef UNDEF_MACRO\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, IfndefRecognized) {
  PreprocFixture f;
  Preprocess("`ifndef UNDEF_MACRO\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, ElseRecognized) {
  PreprocFixture f;
  Preprocess("`ifdef UNDEF_MACRO\n`else\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, ElsifRecognized) {
  PreprocFixture f;
  Preprocess("`ifdef UNDEF_MACRO\n`elsif UNDEF_MACRO\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, EndifRecognized) {
  PreprocFixture f;
  Preprocess("`ifdef UNDEF_MACRO\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, TimescaleRecognized) {
  PreprocFixture f;
  Preprocess("`timescale 1ns / 1ps\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, ResetallRecognized) {
  PreprocFixture f;
  Preprocess("`resetall\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, CelldefineRecognized) {
  PreprocFixture f;
  Preprocess("`celldefine\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, EndcelldefineRecognized) {
  PreprocFixture f;
  Preprocess("`endcelldefine\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, DefaultNettypeRecognized) {
  PreprocFixture f;
  Preprocess("`default_nettype wire\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, UnconnectedDriveRecognized) {
  PreprocFixture f;
  Preprocess("`unconnected_drive pull0\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, NounconnectedDriveRecognized) {
  PreprocFixture f;
  Preprocess("`nounconnected_drive\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, PragmaRecognized) {
  PreprocFixture f;
  Preprocess("`pragma protect begin\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, LineRecognized) {
  PreprocFixture f;
  Preprocess("`line 1 \"test.sv\" 0\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, BeginKeywordsRecognized) {
  PreprocFixture f;
  Preprocess("`begin_keywords \"1800-2023\"\n`end_keywords\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, EndKeywordsRecognized) {
  PreprocFixture f;
  Preprocess("`begin_keywords \"1800-2023\"\n`end_keywords\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, FileRecognized) {
  PreprocFixture f;
  auto result = Preprocess("int x = `__FILE__;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("<test>"), std::string::npos);
}

TEST(Preprocessor, LineeMacroRecognized) {
  PreprocFixture f;
  Preprocess("int x = `__LINE__;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_define) {
  PreprocFixture f;
  Preprocess("`define define 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_undef) {
  PreprocFixture f;
  Preprocess("`define undef 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_undefineall) {
  PreprocFixture f;
  Preprocess("`define undefineall 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_ifdef) {
  PreprocFixture f;
  Preprocess("`define ifdef 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_ifndef) {
  PreprocFixture f;
  Preprocess("`define ifndef 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_elsif) {
  PreprocFixture f;
  Preprocess("`define elsif 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_else) {
  PreprocFixture f;
  Preprocess("`define else 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_endif) {
  PreprocFixture f;
  Preprocess("`define endif 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_include) {
  PreprocFixture f;
  Preprocess("`define include 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_timescale) {
  PreprocFixture f;
  Preprocess("`define timescale 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_resetall) {
  PreprocFixture f;
  Preprocess("`define resetall 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_celldefine) {
  PreprocFixture f;
  Preprocess("`define celldefine 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_endcelldefine) {
  PreprocFixture f;
  Preprocess("`define endcelldefine 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_default_nettype) {
  PreprocFixture f;
  Preprocess("`define default_nettype 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_unconnected_drive) {
  PreprocFixture f;
  Preprocess("`define unconnected_drive 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_nounconnected_drive) {
  PreprocFixture f;
  Preprocess("`define nounconnected_drive 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_pragma) {
  PreprocFixture f;
  Preprocess("`define pragma 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_line) {
  PreprocFixture f;
  Preprocess("`define line 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_begin_keywords) {
  PreprocFixture f;
  Preprocess("`define begin_keywords 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, CannotRedefine_end_keywords) {
  PreprocFixture f;
  Preprocess("`define end_keywords 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, IncludeRecognized) {
  IncludeTestDir tmp;
  tmp.WriteFile("empty.svh", "\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile(tmp.dir / "top.sv", "`include \"empty.svh\"\n");
  Preprocessor pp(f.mgr, f.diag, {});
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, UnknownBacktickNameNotTreatedAsDirective) {
  PreprocFixture f;
  auto result = Preprocess("int x = `foobar;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("`foobar"), std::string::npos);
}

TEST(Preprocessor, UserMacroNotConfusedWithDirective) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define MY_DIRECTIVE 42\n"
      "int x = `MY_DIRECTIVE;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("42"), std::string::npos);
}

TEST(Preprocessor, IncludeWithAngleBrackets) {
  PreprocFixture f;

  Preprocess("`include <nonexistent.svh>\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}
