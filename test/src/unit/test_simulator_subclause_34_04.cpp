#include <gtest/gtest.h>

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "preprocessor/preprocessor.h"

namespace fs = std::filesystem;

namespace {

struct DesignRun {
  SimFixture f;
  Preprocessor pp{f.mgr, f.diag, {}};
  uint64_t result = 0;

  explicit DesignRun(const std::string& src) {
    result = RunPreprocessedSim(f, f.mgr.AddFile("<test>", src), "result", pp);
  }

  DesignRun(const std::string& path, const std::string& src) {
    result = RunPreprocessedSim(f, f.mgr.AddFile(path, src), "result", pp);
  }
};

struct IncludeTestDir {
  fs::path dir;

  explicit IncludeTestDir(const std::string& name) {
    dir = fs::temp_directory_path() / ("delta_protect_sim_34_04_" + name);
    fs::create_directories(dir);
  }

  ~IncludeTestDir() { fs::remove_all(dir); }

  std::string WriteBody(const std::string& content) {
    std::ofstream ofs(dir / "body.svh");
    ofs << content;
    return (dir / "top.sv").string();
  }
};

TEST(ProtectPragmaDirectivesSimulation, ARegionMayCloseAfterTheModuleEnds) {
  DesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "endmodule\n"
      "`pragma protect end\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(ProtectPragmaDirectivesSimulation, ARegionMayOpenBeforeTheModuleBegins) {
  DesignRun run(
      "`pragma protect begin\n"
      "module t;\n"
      "  int result = 1;\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(ProtectPragmaDirectivesSimulation, ARegionMaySpanTwoModules) {
  DesignRun run(
      "module a;\n"
      "`pragma protect begin\n"
      "  int unused = 7;\n"
      "endmodule\n"
      "module t;\n"
      "  int result = 1;\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(ProtectPragmaDirectivesSimulation, ARegionMayOpenInsideANamedBlock) {
  DesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "  initial begin : blk\n"
      "`pragma protect begin\n"
      "    result = 42;\n"
      "  end\n"
      "endmodule\n"
      "`pragma protect end\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(ProtectPragmaDirectivesSimulation, DescribingKeywordsReachNoDesign) {
  DesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect author=\"Acme\", author_info=\"IP group\"\n"
      "`pragma protect encoding=(enctype=\"raw\", bytes=190)\n"
      "`pragma protect data_method=des_cbc\n"
      "`pragma protect comment=1997\n"
      "`pragma protect data_public_key\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "`pragma protect reset\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(ProtectPragmaDirectivesSimulation, ADirectiveOfAnotherPragmaDelimitsNone) {
  DesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma acme_tool begin\n"
      "  initial result = 42;\n"
      "`pragma acme_tool end\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(ProtectPragmaDirectivesSimulation, ARegionMayCloseInsideAnIncludedFile) {
  IncludeTestDir tmp("region_into_include");
  std::string body =
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n";
  std::string src =
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "`include \"body.svh\"\n";

  DesignRun run(tmp.WriteBody(body), src);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(ProtectPragmaDirectivesSimulation, ARegionMayOpenInsideAnIncludedFile) {
  IncludeTestDir tmp("region_out_of_include");
  std::string body =
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n";
  std::string src =
      "`include \"body.svh\"\n"
      "`pragma protect end\n"
      "endmodule\n";

  DesignRun run(tmp.WriteBody(body), src);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

}  // namespace
