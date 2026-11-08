#include <gtest/gtest.h>
#include <unistd.h>

#include <filesystem>
#include <fstream>
#include <string>
#include <utility>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "preprocessor/preprocessor.h"

namespace fs = std::filesystem;

struct KeywordSimIncludeDir {
  fs::path dir;

  KeywordSimIncludeDir() {
    dir = fs::temp_directory_path() /
          ("delta_kwsim_22_14_" + std::to_string(getpid()));
    fs::create_directories(dir);
  }

  ~KeywordSimIncludeDir() { fs::remove_all(dir); }

  void Write(const std::string& name, const std::string& content) {
    std::ofstream ofs(dir / name);
    ofs << content;
  }
};

TEST(KeywordVersionSimulation, KeywordRegionDoesNotChangeComputedValue) {
  auto guarded = PreprocessAndGet(
      "`begin_keywords \"1364-2001\"\n"
      "module t;\n"
      "  wire logic;\n"
      "  reg [15:0] result;\n"
      "  initial result = 16'd7 * 16'd6 + 16'd1;\n"
      "endmodule\n"
      "`end_keywords\n",
      "result");
  EXPECT_EQ(guarded, 43u);

  auto plain = PreprocessAndGet(
      "module t;\n"
      "  logic [15:0] result;\n"
      "  initial result = 16'd7 * 16'd6 + 16'd1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(plain, guarded);
}

TEST(KeywordVersionSimulation, OldVersionIdentifierIsAnExpressionOperand) {
  auto result = PreprocessAndGet(
      "`begin_keywords \"1364-2001\"\n"
      "module t;\n"
      "  wire [7:0] logic;\n"
      "  reg [7:0] result;\n"
      "  assign logic = 8'd5;\n"
      "  initial #1 result = logic * 8'd3 + 8'd2;\n"
      "endmodule\n"
      "`end_keywords\n",
      "result");
  EXPECT_EQ(result, 17u);
}

TEST(KeywordVersionSimulation, NestedRegionsSimulate) {
  auto result = PreprocessAndGet(
      "`begin_keywords \"1800-2012\"\n"
      "`begin_keywords \"1364-2001\"\n"
      "module inner (output reg [7:0] o);\n"
      "  wire logic;\n"
      "  initial o = 8'd21;\n"
      "endmodule\n"
      "`end_keywords\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  inner i (.o(result));\n"
      "endmodule\n"
      "`end_keywords\n",
      "result");
  EXPECT_EQ(result, 21u);
}

TEST(KeywordVersionSimulation, RegionReachesIntoIncludedFile) {
  KeywordSimIncludeDir tmp;
  tmp.Write("driver.svh",
            "module driver (output reg [7:0] o);\n"
            "  wire logic;\n"
            "  initial o = 8'd57;\n"
            "endmodule\n");

  SimFixture f;
  auto fid = f.mgr.AddFile("<test>",
                           "`begin_keywords \"1364-2001\"\n"
                           "`include \"driver.svh\"\n"
                           "`end_keywords\n"
                           "module t;\n"
                           "  logic [7:0] result;\n"
                           "  driver d (.o(result));\n"
                           "endmodule\n");

  PreprocConfig config;
  config.include_dirs.push_back(tmp.dir.string());
  Preprocessor pp(f.mgr, f.diag, std::move(config));
  auto result = RunPreprocessedSim(f, fid, "result", pp);
  pp.ReportUnterminatedKeywordRegions();
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result, 57u);
}
