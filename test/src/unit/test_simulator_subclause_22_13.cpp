#include <gtest/gtest.h>

#include <cstdio>
#include <filesystem>
#include <fstream>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "preprocessor/preprocessor.h"

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
