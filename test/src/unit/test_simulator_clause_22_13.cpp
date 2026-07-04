#include <filesystem>
#include <fstream>

#include "helpers_preprocess_and_get.h"

TEST(FileAndLineMacroSimulation, LineExpandsToCorrectValue) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  initial result = `__LINE__;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 3u);
}

TEST(FileAndLineMacroSimulation, LineValueDiffersPerLine) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  logic [31:0] dummy;\n"
      "  initial begin\n"
      "    dummy = `__LINE__;\n"
      "    result = `__LINE__;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 6u);
}

// Claim A: `__FILE__ expands "in the form of a string literal". The
// preprocessor tests observe the literal text; this drives that expansion
// through the full pipeline to confirm the produced token is a genuine,
// consumable SV string literal. The top source is registered as "<test>", so
// the expansion equals that path and the string comparison holds.
TEST(FileAndLineMacroSimulation, FileExpandsToConsumableStringLiteral) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "  logic result;\n"
      "  string s;\n"
      "  initial begin\n"
      "    s = `__FILE__;\n"
      "    result = (s == \"<test>\");\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 1u);
}

// Claim E, end-to-end through the §22.12 `line dependency: a `line directive
// renumbers the following line, and `__LINE__ must reflect that override. Built
// from real `line syntax and driven through parse/elaborate/run so the observed
// simulated value (500, not the natural source line 4) confirms the macro
// consumed the overridden number.
TEST(FileAndLineMacroSimulation, LineDirectiveOverridesLineValueEndToEnd) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  `line 500 \"renamed.sv\" 0\n"
      "  initial result = `__LINE__;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 500u);
}

// Claim D, end-to-end through the §22.4 `include dependency: while processing
// an included file, `__LINE__ corresponds to that file. The macro sits on line
// 5 of the included file (padded), so the simulated value discriminates the
// included file's line from the `include site's line 3 in the top source.
TEST(FileAndLineMacroSimulation, IncludedFileLineValueEndToEnd) {
  std::string tmp_dir = "/tmp/dhl_22_13_sim_include";
  std::string inc_path = tmp_dir + "/incline.svh";
  std::filesystem::create_directories(tmp_dir);
  {
    std::ofstream ofs(inc_path);
    ofs << "// pad a\n"
        << "// pad b\n"
        << "// pad c\n"
        << "// pad d\n"
        << "initial result = `__LINE__;\n";
  }

  SimFixture f;
  auto fid = f.mgr.AddFile("<test>",
                           "module t;\n"
                           "  logic [31:0] result;\n"
                           "  `include \"incline.svh\"\n"
                           "endmodule\n");
  PreprocConfig cfg;
  cfg.include_dirs.push_back(tmp_dir);
  Preprocessor pp(f.mgr, f.diag, cfg);
  auto result = RunPreprocessedSim(f, fid, "result", pp);
  EXPECT_EQ(result, 5u);

  std::remove(inc_path.c_str());
  std::remove(tmp_dir.c_str());
}
