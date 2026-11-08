#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_processing.h"

namespace {

constexpr std::string_view kAuthorKey = "acme-exchange-key";

struct ProtectedDesignRun {
  SimFixture f;
  Preprocessor pp;
  uint64_t result = 0;

  explicit ProtectedDesignRun(const std::string& src)
      : pp(f.mgr, f.diag, ReadingKey()) {
    auto fid = f.mgr.AddFile("<test>", EncryptEnvelopes(src, kAuthorKey));
    result = RunPreprocessedSim(f, fid, "result", pp);
  }

  static PreprocConfig ReadingKey() {
    PreprocConfig config;
    config.protect_key = kAuthorKey;
    return config;
  }
};

TEST(ProtectEndDescriptionSimulation, TheTwoHalvesOfThePointAreOneDesign) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "  int addend = 7;\n"
      "`pragma protect end\n"
      "  initial result = addend * 6;\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(ProtectEndDescriptionSimulation, WhatTheRegionHeldIsInEffectAfterIt) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "`define SCALE 6\n"
      "`pragma protect end\n"
      "  int addend = 7;\n"
      "  initial result = addend * `SCALE;\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(ProtectEndDescriptionSimulation, ADesignDividedTwiceRunsAsOne) {
  ProtectedDesignRun run(
      "module t;\n"
      "  int result = 1;\n"
      "`pragma protect begin\n"
      "  int addend = 7;\n"
      "`pragma protect end\n"
      "  int scale = 6;\n"
      "`pragma protect begin\n"
      "  initial result = addend * scale;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

TEST(ProtectEndDescriptionSimulation, ADoublySealedDesignReturnsEveryZone) {
  std::string sealed = "`pragma protect begin\n";
  sealed.append("  int addend = 7;\n");
  sealed.append("`pragma protect end\n");
  std::string src = "module t;\n";
  src.append("  int result = 1;\n");
  src.append("`pragma protect begin\n");
  src.append(EncryptEnvelopes(sealed, kAuthorKey));
  src.append("  int scale = 6;\n");
  src.append("`pragma protect end\n");
  src.append("  initial result = addend * scale;\n");
  src.append("endmodule\n");
  ProtectedDesignRun run(src);
  EXPECT_FALSE(run.f.diag.HasErrors());
  EXPECT_EQ(run.result, 42U);
}

}  // namespace
