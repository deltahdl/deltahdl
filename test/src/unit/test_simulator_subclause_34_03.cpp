#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_processing.h"

namespace {

constexpr std::string_view kAuthorKey = "acme-exchange-key";
constexpr std::string_view kStrangerKey = "not-the-authors-key";

PreprocConfig KeyConfig(std::string_view key) {
  PreprocConfig config;
  config.protect_key = key;
  return config;
}

struct ProtectedDesignRun {
  SimFixture f;
  Preprocessor pp;
  uint64_t result = 0;

  ProtectedDesignRun(const std::string& src, std::string_view key)
      : pp(f.mgr, f.diag, KeyConfig(key)) {
    auto fid = f.mgr.AddFile("<test>", EncryptEnvelopes(src, kAuthorKey));
    result = RunPreprocessedSim(f, fid, "result", pp);
  }
};

TEST(ProtectedEnvelopeProcessingSimulation, ProtectedDesignRunsWithTheKey) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n",
      kAuthorKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(ProtectedEnvelopeProcessingSimulation, ProtectedDesignStaysSealedWithout) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n",
      kStrangerKey);
  EXPECT_TRUE(ReportedError(
      run.f.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied", 10,
      "34.3.2"));
  EXPECT_EQ(run.result, 1U);
}

TEST(ProtectedEnvelopeProcessingSimulation, EveryEnvelopeOfADesignArrives) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "  int addend = 7;\n"
      "`pragma protect end\n"
      "`pragma protect begin\n"
      "  int scale = 6;\n"
      "`pragma protect end\n"
      "  initial result = addend * scale;\n"
      "endmodule\n",
      kAuthorKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(ProtectedEnvelopeProcessingSimulation, MacroInsideTheRegionExpandsAfter) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "`define ANSWER 42\n"
      "  initial result = `ANSWER;\n"
      "`pragma protect end\n"
      "endmodule\n",
      kAuthorKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(ProtectedEnvelopeProcessingSimulation, ResettingDirectivesKeepsTheKey) {
  ProtectedDesignRun run(
      "`pragma protect begin\n"
      "`define ANSWER 42\n"
      "`pragma protect end\n"
      "`resetall\n"
      "`pragma protect begin\n"
      "module t;\n"
      "  int result = 1;\n"
      "  initial result = `ANSWER;\n"
      "endmodule\n"
      "`pragma protect end\n",
      kAuthorKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(ProtectedEnvelopeProcessingSimulation, DescribingExpressionsChangeNone) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect author=\"Acme Corp\"\n"
      "`pragma protect data_method=\"x-caesar\", begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n",
      kAuthorKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

}  // namespace
