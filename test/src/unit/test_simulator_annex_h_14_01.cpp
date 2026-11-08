#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/dpi_runtime.h"

extern "C" const char* svDpiVersion(void);

using namespace delta;

namespace {

TEST(DpiCompatibility, TheVersionStringTellsTheLevel) {
  EXPECT_STREQ(svDpiVersion(), "1800-2005");
  EXPECT_EQ(DpiCompatibilityLevelOf(svDpiVersion()),
            DpiCompatibilityLevel::kIeee1800);
  EXPECT_EQ(DpiCompatibilityLevelOf("SV3.1a"), DpiCompatibilityLevel::kSv31a);
  EXPECT_FALSE(DpiOpaqueHandlesAreRequiredForAllPackedArguments(
      DpiCompatibilityLevel::kIeee1800));
  EXPECT_TRUE(DpiOpaqueHandlesAreRequiredForAllPackedArguments(
      DpiCompatibilityLevel::kSv31a));
}

TEST(DpiCompatibility, TheSpecStringSelectsThePassingSemantics) {
  EXPECT_EQ(DpiPassingSemanticsOfSpecString("DPI"),
            DpiPackedArgPassing::kSv31aReference);
  EXPECT_EQ(DpiPassingSemanticsOfSpecString("DPI-C"),
            DpiPackedArgPassing::kCanonical);
}

TEST(DpiCompatibility, TheSv31aDefinitionsAreOptionalAndBindingMayFail) {
  EXPECT_FALSE(DpiSv31aDefinitionsAreObligatoryInSvdpiH());
  EXPECT_TRUE(DpiCCodeMayFailToBind(false));
  EXPECT_FALSE(DpiCCodeMayFailToBind(true));
}

TEST(DpiCompatibility, ADesignsDeclarationsSelectTheirSemanticsPerFunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  import \"DPI\" function void legacy(input bit [7:0] v);\n"
      "  import \"DPI-C\" function void current(input bit [7:0] v);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* dpi = f.ctx.GetDpiRuntime();
  ASSERT_NE(dpi, nullptr);
  const DpiRtFunction* legacy = dpi->FindImport("legacy");
  ASSERT_NE(legacy, nullptr);
  EXPECT_EQ(legacy->packed_arg_passing, DpiPackedArgPassing::kSv31aReference);
  const DpiRtFunction* current = dpi->FindImport("current");
  ASSERT_NE(current, nullptr);
  EXPECT_EQ(current->packed_arg_passing, DpiPackedArgPassing::kCanonical);
}

}  // namespace
