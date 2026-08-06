#include <gtest/gtest.h>

#include <filesystem>
#include <fstream>

#include "fixture_preprocessor.h"

using namespace delta;

TEST(FileAndLineMacroPreprocessing, File_ExpandsToStringLiteral) {
  PreprocFixture f;
  auto result = Preprocess("`__FILE__\n", f);

  EXPECT_NE(result.find("\"<test>\""), std::string::npos);
}

TEST(FileAndLineMacroPreprocessing, File_UsesToolOpenedPath) {
  PreprocFixture f;
  auto fid = f.mgr.AddFile("/full/path/to/design.sv", "`__FILE__\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);
  EXPECT_NE(result.find("\"/full/path/to/design.sv\""), std::string::npos);
}

TEST(FileAndLineMacroPreprocessing, Line_ExpandsOnSecondLine) {
  PreprocFixture f;
  auto result = Preprocess("line1\n`__LINE__\n", f);
  EXPECT_NE(result.find('2'), std::string::npos);
}

TEST(FileAndLineMacroPreprocessing, File_InlineInExpression) {
  PreprocFixture f;
  auto result = Preprocess("$display(`__FILE__);\n", f);
  EXPECT_NE(result.find("$display(\"<test>\");"), std::string::npos);
}

TEST(FileAndLineMacroPreprocessing, Line_InlineInExpression) {
  PreprocFixture f;
  auto result = Preprocess("$display(`__LINE__);\n", f);
  EXPECT_NE(result.find("$display(1);"), std::string::npos);
}

TEST(FileAndLineMacroPreprocessing, FileAndLine_SameLine) {
  PreprocFixture f;
  auto result = Preprocess("$display(`__FILE__, `__LINE__);\n", f);
  EXPECT_NE(result.find("\"<test>\""), std::string::npos);
  EXPECT_NE(result.find('1'), std::string::npos);
}

TEST(FileAndLineMacroPreprocessing, Line_DifferentValuesOnDifferentLines) {
  PreprocFixture f;
  auto result = Preprocess("`__LINE__\n`__LINE__\n`__LINE__\n", f);
  EXPECT_NE(result.find('1'), std::string::npos);
  EXPECT_NE(result.find('2'), std::string::npos);
  EXPECT_NE(result.find('3'), std::string::npos);
}

TEST(FileAndLineMacroPreprocessing, LineDirective_AffectsLineMacro) {
  PreprocFixture f;
  auto result = Preprocess("`line 100 \"test.sv\" 0\n`__LINE__\n", f);

  EXPECT_NE(result.find("100"), std::string::npos);
}

TEST(FileAndLineMacroPreprocessing, LineDirective_AffectsFileMacro) {
  PreprocFixture f;
  auto result = Preprocess("`line 1 \"overridden.sv\" 0\n`__FILE__\n", f);
  EXPECT_NE(result.find("\"overridden.sv\""), std::string::npos);
}

TEST(FileAndLineMacroPreprocessing, Include_ChangesFileAndLine) {
  std::string tmp_dir = "/tmp/deltahdl_test_22_13";
  std::string inc_path = tmp_dir + "/inc.svh";
  std::filesystem::create_directories(tmp_dir);
  {
    std::ofstream ofs(inc_path);
    ofs << "`__FILE__\n`__LINE__\n";
  }

  PreprocFixture f;
  PreprocConfig cfg;
  cfg.include_dirs.push_back(tmp_dir);
  auto result = Preprocess("`include \"inc.svh\"\n", f, cfg);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("inc.svh"), std::string::npos);

  EXPECT_NE(result.find('1'), std::string::npos);
  EXPECT_NE(result.find('2'), std::string::npos);

  std::remove(inc_path.c_str());
  std::remove(tmp_dir.c_str());
}

TEST(FileAndLineMacroPreprocessing, Include_RevertsAfterInclude) {
  std::string tmp_dir = "/tmp/deltahdl_test_22_13_revert";
  std::string inc_path = tmp_dir + "/empty.svh";
  std::filesystem::create_directories(tmp_dir);
  {
    std::ofstream ofs(inc_path);
    ofs << "// included\n";
  }

  PreprocFixture f;
  PreprocConfig cfg;
  cfg.include_dirs.push_back(tmp_dir);

  auto result =
      Preprocess("`__FILE__\n`include \"empty.svh\"\n`__FILE__\n", f, cfg);
  EXPECT_FALSE(f.diag.HasErrors());

  size_t first = result.find("\"<test>\"");
  EXPECT_NE(first, std::string::npos);
  size_t second = result.find("\"<test>\"", first + 1);
  EXPECT_NE(second, std::string::npos);

  std::remove(inc_path.c_str());
  std::remove(tmp_dir.c_str());
}

TEST(FileAndLineMacroPreprocessing, FileAndLine_InsideIfdef) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ACTIVE\n`ifdef ACTIVE\n`__FILE__\n`__LINE__\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\"<test>\""), std::string::npos);

  EXPECT_NE(result.find('4'), std::string::npos);
}

TEST(FileAndLineMacroPreprocessing, FileAndLine_InsideInactiveIfdef) {
  PreprocFixture f;
  auto result = Preprocess("`ifdef UNDEF\n`__FILE__\n`__LINE__\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_EQ(result.find("\"<test>\""), std::string::npos);
}

TEST(FileAndLineMacroPreprocessing, File_CannotRedefine) {
  PreprocFixture f;
  Preprocess("`define __FILE__ \"bad\"\n", f);

  auto result = Preprocess("`__FILE__\n", f);

  EXPECT_NE(result.find('"'), std::string::npos);
}

TEST(FileAndLineMacroPreprocessing, File_MultipleOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess("`__FILE__ `__FILE__\n", f);
  size_t first = result.find("\"<test>\"");
  EXPECT_NE(first, std::string::npos);
  size_t second = result.find("\"<test>\"", first + 1);
  EXPECT_NE(second, std::string::npos);
}

TEST(FileAndLineMacroPreprocessing, Line_StandaloneDirective) {
  PreprocFixture f;
  auto result = Preprocess("`__LINE__\n", f);
  auto trimmed = result;
  trimmed.erase(0, trimmed.find_first_not_of(" \t\n\r"));
  trimmed.erase(trimmed.find_last_not_of(" \t\n\r") + 1);
  EXPECT_EQ(trimmed, "1");
}

TEST(FileAndLineMacroPreprocessing, File_IncludeShowsResolvedNotShortName) {
  std::string tmp_dir = "/tmp/deltahdl_test_22_13_resolved";
  std::string inc_path = tmp_dir + "/short.svh";
  std::filesystem::create_directories(tmp_dir);
  {
    std::ofstream ofs(inc_path);
    ofs << "`__FILE__\n";
  }

  PreprocFixture f;
  PreprocConfig cfg;
  cfg.include_dirs.push_back(tmp_dir);
  auto result = Preprocess("`include \"short.svh\"\n", f, cfg);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find(tmp_dir), std::string::npos);

  std::remove(inc_path.c_str());
  std::remove(tmp_dir.c_str());
}

TEST(FileAndLineMacroPreprocessing, Include_LineExpandsToIncludedFileLine) {
  std::string tmp_dir = "/tmp/dhl_22_13_inner_line";
  std::string inc_path = tmp_dir + "/x.svh";
  std::filesystem::create_directories(tmp_dir);
  {
    std::ofstream ofs(inc_path);
    for (int i = 0; i < 6; ++i) ofs << "// pad\n";
    ofs << "`__LINE__\n";
  }

  PreprocFixture f;
  PreprocConfig cfg;
  cfg.include_dirs.push_back(tmp_dir);
  auto result = Preprocess("`include \"x.svh\"\n", f, cfg);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("\n7\n"), std::string::npos);

  std::remove(inc_path.c_str());
  std::remove(tmp_dir.c_str());
}

TEST(FileAndLineMacroPreprocessing, Include_LineRevertsWithLongInclude) {
  std::string tmp_dir = "/tmp/deltahdl_test_22_13_revert_long";
  std::string inc_path = tmp_dir + "/long.svh";
  std::filesystem::create_directories(tmp_dir);
  {
    std::ofstream ofs(inc_path);
    for (int i = 0; i < 50; ++i) ofs << "// padding " << i << "\n";
  }

  PreprocFixture f;
  PreprocConfig cfg;
  cfg.include_dirs.push_back(tmp_dir);

  auto result = Preprocess("`include \"long.svh\"\n`__LINE__\n", f, cfg);
  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("\n2\n"), std::string::npos);
  EXPECT_EQ(result.find("51"), std::string::npos);

  std::remove(inc_path.c_str());
  std::remove(tmp_dir.c_str());
}
