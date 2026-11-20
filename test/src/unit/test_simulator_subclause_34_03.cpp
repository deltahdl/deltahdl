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

void ExpectTheSealedItemsToRun(const std::string& src) {
  ProtectedDesignRun run(src, kAuthorKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(ProtectedEnvelopeProcessingSimulation, ItemsSealedInAPackageRun) {
  ExpectTheSealedItemsToRun(
      "package sealed_pkg;\n"
      "`pragma protect begin\n"
      "  function automatic int answer(); return 42; endfunction\n"
      "`pragma protect end\n"
      "endpackage\n"
      "module t;\n"
      "  int result = 1;\n"
      "  initial result = sealed_pkg::answer();\n"
      "endmodule\n");
}

TEST(ProtectedEnvelopeProcessingSimulation, ItemsSealedInAnInterfaceRun) {
  ExpectTheSealedItemsToRun(
      "interface sealed_if;\n"
      "`pragma protect begin\n"
      "  int answer = 42;\n"
      "`pragma protect end\n"
      "endinterface\n"
      "module t;\n"
      "  sealed_if u();\n"
      "  int result = 1;\n"
      "  initial #1 result = u.answer;\n"
      "endmodule\n");
}

TEST(ProtectedEnvelopeProcessingSimulation, ItemsSealedInAProgramRun) {
  ExpectTheSealedItemsToRun(
      "program sealed_pr(output int answer);\n"
      "`pragma protect begin\n"
      "  initial answer = 42;\n"
      "`pragma protect end\n"
      "endprogram\n"
      "module t;\n"
      "  int result;\n"
      "  sealed_pr p(result);\n"
      "endmodule\n");
}

TEST(ProtectedEnvelopeProcessingSimulation, ItemsSealedInAClassRun) {
  ExpectTheSealedItemsToRun(
      "module t;\n"
      "  class sealed_c;\n"
      "`pragma protect begin\n"
      "    function int answer(); return 42; endfunction\n"
      "`pragma protect end\n"
      "  endclass\n"
      "  int result = 1;\n"
      "  initial begin\n"
      "    sealed_c c;\n"
      "    c = new;\n"
      "    result = c.answer();\n"
      "  end\n"
      "endmodule\n");
}

TEST(ProtectedEnvelopeProcessingSimulation, AFunctionBodySealedRuns) {
  ExpectTheSealedItemsToRun(
      "module t;\n"
      "  function automatic int answer();\n"
      "`pragma protect begin\n"
      "    return 42;\n"
      "`pragma protect end\n"
      "  endfunction\n"
      "  int result = 1;\n"
      "  initial result = answer();\n"
      "endmodule\n");
}

TEST(ProtectedEnvelopeProcessingSimulation, ATaskBodySealedRuns) {
  ExpectTheSealedItemsToRun(
      "module t;\n"
      "  int result = 1;\n"
      "  task automatic deliver();\n"
      "`pragma protect begin\n"
      "    result = 42;\n"
      "`pragma protect end\n"
      "  endtask\n"
      "  initial deliver();\n"
      "endmodule\n");
}

}  // namespace
