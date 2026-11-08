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

constexpr std::string_view kExchangeKey = "acme-exchange-key";
constexpr std::string_view kOtherKey = "not-the-authors-key";

constexpr std::string_view kRecoveredBlockAnnouncement =
    "`pragma protect data_block\n";

PreprocConfig KeyConfig(std::string_view key) {
  PreprocConfig config;
  config.protect_key = key;
  return config;
}

std::string EnvelopeOf(const std::string& body) {
  std::string region = "`pragma protect begin\n";
  region += body;
  region += "`pragma protect end\n";
  return EncryptEnvelopes(region, kExchangeKey);
}

struct RecoveredDesignRun {
  SimFixture f;
  Preprocessor pp;
  uint64_t result = 0;

  RecoveredDesignRun(const std::string& src, std::string_view key)
      : pp(f.mgr, f.diag, KeyConfig(key)) {
    auto fid = f.mgr.AddFile("<test>", src);
    result = RunPreprocessedSim(f, fid, "result", pp);
  }
};

TEST(EnvelopeDecryptionSimulation, AMacroInARecoveredDesignReachesTheRun) {
  std::string src = "`define ANSWER 42\n";
  src += "module t;\n";
  src += "  int result = 1;\n";
  src += EnvelopeOf("  initial result = `ANSWER;\n");
  src += "endmodule\n";
  RecoveredDesignRun run(src, kExchangeKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(EnvelopeDecryptionSimulation, ADesignInAnEnclosedEnvelopeReachesTheRun) {
  std::string sealed = EnvelopeOf("  initial result = 42;\n");
  std::string src = "module t;\n";
  src += "  int result = 1;\n";
  src += EnvelopeOf(sealed);
  src += "endmodule\n";
  RecoveredDesignRun run(src, kExchangeKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(EnvelopeDecryptionSimulation, AnEnclosedDesignStaysSealedUnderAnotherKey) {
  std::string sealed = EnvelopeOf("  initial result = 42;\n");
  std::string src = "module t;\n";
  src += "  int result = 1;\n";
  src += EnvelopeOf(sealed);
  src += "endmodule\n";
  RecoveredDesignRun run(src, kOtherKey);
  EXPECT_TRUE(ReportedError(
      run.f.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      LineHolding(src, kRecoveredBlockAnnouncement) + 1, "34.3.2"));
  EXPECT_EQ(run.result, 1U);
}

TEST(EnvelopeDecryptionSimulation, AMacroSealedTwoEnvelopesDeepReachesTheRun) {
  std::string sealed = EnvelopeOf("  initial result = `ANSWER;\n");
  std::string body = "`define ANSWER 42\n";
  body += sealed;
  std::string src = "module t;\n";
  src += "  int result = 1;\n";
  src += EnvelopeOf(body);
  src += "endmodule\n";
  RecoveredDesignRun run(src, kExchangeKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(EnvelopeDecryptionSimulation, AWholeSealedModuleReachesTheRun) {
  std::string body = "module t;\n";
  body += "  int result = 42;\n";
  body += "endmodule\n";
  RecoveredDesignRun run(EnvelopeOf(body), kExchangeKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(EnvelopeDecryptionSimulation, AStringSpecifiedEnvelopeDeliversItsDesign) {
  std::string authored = "module t;\n";
  authored += "  int result = 7;\n";
  authored += "`pragma protect author=\"Widget Works\"\n";
  authored += "`pragma protect data_keyowner=\"Widget Works\", begin\n";
  authored += "  initial result = 99;\n";
  authored += "`pragma protect end\n";
  authored += "endmodule\n";
  std::string src = EncryptEnvelopes(authored, kExchangeKey);
  RecoveredDesignRun run(src, kExchangeKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 99U);
}

TEST(EnvelopeDecryptionSimulation, AListSpecifiedEnvelopeDeliversItsDesign) {
  std::string authored = "module t;\n";
  authored += "  int result = 7;\n";
  authored += "`pragma protect decrypt_license=(library=\"dec.so\", ";
  authored += "entry=\"check\", feature=\"core\"), begin\n";
  authored += "  initial result = 99;\n";
  authored += "`pragma protect end\n";
  authored += "endmodule\n";
  std::string src = EncryptEnvelopes(authored, kExchangeKey);
  RecoveredDesignRun run(src, kExchangeKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 99U);
}

}  // namespace
