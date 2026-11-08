#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

namespace {

constexpr std::string_view kAuthorKey = "acme-exchange-key";

constexpr std::string_view kKeyProvider = "aegis-custody";
constexpr std::string_view kKeyProviderKeyName = "wrapping-2026";
constexpr std::string_view kKeyProviderKey = "aegis-custody-wrapping-key";

PreprocConfig KeyConfig(std::string_view key) {
  PreprocConfig config;
  config.protect_key = key;
  return config;
}

struct ProtectedDesignRun {
  SimFixture f;
  Preprocessor pp;
  uint64_t result = 0;

  explicit ProtectedDesignRun(const std::string& src)
      : pp(f.mgr, f.diag, KeyConfig(kAuthorKey)) {
    auto fid = f.mgr.AddFile("<test>", EncryptEnvelopes(src, kAuthorKey));
    result = RunPreprocessedSim(f, fid, "result", pp);
  }
};

struct KeyBlockDesignRun {
  SimFixture f;
  Preprocessor pp;
  uint64_t result = 0;

  KeyBlockDesignRun(const std::string& src, const ProtectKeyList& keys)
      : pp(f.mgr, f.diag, ListConfig(keys)) {
    auto fid = f.mgr.AddFile("<test>", EncryptEnvelopes(src, "", keys));
    result = RunPreprocessedSim(f, fid, "result", pp);
  }

  static PreprocConfig ListConfig(const ProtectKeyList& keys) {
    PreprocConfig config;
    config.protect_keys = keys;
    return config;
  }
};

TEST(ProtectBeginDescriptionSimulation, TheTwoHalvesOfThePointAreOneDesign) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "  int addend = 7;\n"
      "`pragma protect begin\n"
      "  initial result = addend * 6;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(ProtectBeginDescriptionSimulation, EveryLineBetweenTheDelimitersReturns) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "  // the multiplier this design was written around\n"
      "`define SCALE 6\n"
      "  int addend = 7;\n"
      "  initial result = addend * `SCALE;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(ProtectBeginDescriptionSimulation, ADesignSealedTwiceOverStillRuns) {
  std::string sealed = "`pragma protect begin\n";
  sealed += "  initial result = 42;\n";
  sealed += "`pragma protect end\n";
  std::string src = "module t;\n  int result = 1;\n";
  src += "`pragma protect begin\n";
  src += EncryptEnvelopes(sealed, kAuthorKey);
  src += "`pragma protect end\nendmodule\n";
  ProtectedDesignRun run(src);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(ProtectBeginDescriptionSimulation, ADesignWhoseKeysTravelInBlocksRuns) {
  ProtectKey held;
  held.owner = kKeyProvider;
  held.name = kKeyProviderKeyName;
  held.key = kKeyProviderKey;
  ProtectKeyList keys;
  keys.Add(held);
  std::string src = "module t;\n  int result = 1;\n";
  src += "`pragma protect begin\n";
  src += "`pragma protect key_keyowner=\"aegis-custody\"\n";
  src += "`pragma protect key_keyname=\"wrapping-2026\"\n";
  src += "  initial result = 42;\n";
  src += "`pragma protect end\nendmodule\n";
  KeyBlockDesignRun run(src, keys);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

}  // namespace
