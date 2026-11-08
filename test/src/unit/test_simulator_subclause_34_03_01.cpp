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

PreprocConfig KeyConfig(std::string_view key) {
  PreprocConfig config;
  config.protect_key = key;
  return config;
}

struct SpecifiedDesignRun {
  SimFixture f;
  Preprocessor pp;
  std::string written;
  uint64_t result = 0;

  SpecifiedDesignRun(const std::string& src, std::string_view key)
      : pp(f.mgr, f.diag, KeyConfig(key)),
        written(EncryptEnvelopes(src, kExchangeKey)) {
    auto fid = f.mgr.AddFile("<test>", written);
    result = RunPreprocessedSim(f, fid, "result", pp);
  }

  uint32_t BlockLine() const {
    return LineHolding(written, "`pragma protect data_block\n") + 1;
  }
};

TEST(EnvelopeEncryptionSimulation, ASpecifiedEnvelopeDeliversItsDesign) {
  SpecifiedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect author=\"Acme Corp\"\n"
      "`pragma protect data_method=\"x-caesar\", "
      "data_keyname=\"rot13\", begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n",
      kExchangeKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(EnvelopeEncryptionSimulation, AParenthesizedValueIsCarriedWhole) {
  SpecifiedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect runtime_license=(library=\"lic.so\", "
      "entry=\"acquire\", feature=\"runIt\"), begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n",
      kExchangeKey);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(EnvelopeEncryptionSimulation, ASpecifiedEnvelopeStaysSealedUnderAnother) {
  SpecifiedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect data_method=\"x-caesar\", "
      "data_keyname=\"rot13\", begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n",
      kOtherKey);
  EXPECT_TRUE(ReportedError(
      run.f.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      run.BlockLine(), "34.3.2"));
  EXPECT_EQ(run.result, 1U);
}

}  // namespace
