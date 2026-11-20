#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_processing.h"

namespace {

struct EnvelopeSimRun {
  SimFixture f;
  Preprocessor pp{f.mgr, f.diag, {}};
  uint64_t result = 0;

  explicit EnvelopeSimRun(const std::string& src) {
    result = RunPreprocessedSim(f, f.mgr.AddFile("<test>", src), "result", pp);
  }

  const ProtectEnvelopeState& Envelopes() const {
    return pp.ProtectEnvelopes();
  }
};

TEST(ProtectedEnvelopeRegionSimulation, EncryptionEnvelopeRegionStillRuns) {
  EnvelopeSimRun run(
      "module t;\n"
      "  int result;\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].mode,
            EnvelopeMode::kEncryption);
}

TEST(ProtectedEnvelopeRegionSimulation, DecryptionEnvelopeRegionStillRuns) {
  EnvelopeSimRun run(
      "module t;\n"
      "  int result;\n"
      "`pragma protect begin_protected\n"
      "  initial result = 17;\n"
      "`pragma protect end_protected\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 17U);
  EXPECT_FALSE(run.Envelopes().InProtectedRegion());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].mode,
            EnvelopeMode::kDecryption);
}

TEST(ProtectedEnvelopeRegionSimulation, EnvelopeKeywordLeavesTheDesignAlone) {
  EnvelopeSimRun run(
      "module t;\n"
      "  int result;\n"
      "`pragma protect data_method = \"aes128-cbc\"\n"
      "`pragma protect begin_protected\n"
      "  initial result = 7;\n"
      "`pragma protect end_protected\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 7U);
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].envelope_keywords,
            std::vector<std::string>{"data_method"});
}

TEST(ProtectedEnvelopeRegionSimulation, NestedEnvelopeRegionsStillRun) {
  EnvelopeSimRun run(
      "module t;\n"
      "  int result;\n"
      "`pragma protect begin_protected\n"
      "`pragma protect begin\n"
      "  initial result = 9;\n"
      "`pragma protect end\n"
      "`pragma protect end_protected\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 9U);
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 2U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].mode,
            EnvelopeMode::kEncryption);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[1].mode,
            EnvelopeMode::kDecryption);
}

TEST(ProtectedEnvelopeRegionSimulation, OneDirectiveCarriesBothExpressions) {
  EnvelopeSimRun run(
      "module t;\n"
      "  int result;\n"
      "`pragma protect data_method = \"aes128-cbc\", begin_protected\n"
      "  initial result = 7;\n"
      "`pragma protect end_protected\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 7U);
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].envelope_keywords,
            std::vector<std::string>{"data_method"});
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].begin_loc.line, 3U);
}

constexpr std::string_view kNestingKey = "acme-nesting-exchange-key";

std::string SealedEightTimes(std::string body) {
  for (size_t level = 0;
       level < ProtectEnvelopeState::kMinNestedDecryptionEnvelopes; ++level) {
    std::string region = "`pragma protect begin\n";
    region.append(body).append("`pragma protect end\n");
    body = EncryptEnvelopes(region, kNestingKey);
  }
  return body;
}

TEST(ProtectedEnvelopeRegionSimulation, EightNestedSealedEnvelopesStillRun) {
  std::string sealed = SealedEightTimes("  initial result = 88;\n");
  ASSERT_EQ(sealed.find("result = 88"), std::string::npos);
  SimFixture f;
  PreprocConfig config;
  config.protect_key = kNestingKey;
  Preprocessor pp{f.mgr, f.diag, config};
  uint64_t result =
      RunPreprocessedSim(f,
                         f.mgr.AddFile("<test>", "module t;\n  int result;\n" +
                                                     sealed + "endmodule\n"),
                         "result", pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result, 88U);
  EXPECT_EQ(pp.ProtectEnvelopes().DecryptionEnvelopeDepth(), 0U);
}

}  // namespace
