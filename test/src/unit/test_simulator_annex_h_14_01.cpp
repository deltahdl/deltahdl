#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/dpi_runtime.h"

// svDpiVersion belongs to svdpi.h, which redefines VPI names the fixture's
// headers bring in; its prototype is what this file needs of it.
extern "C" const char* svDpiVersion(void);

using namespace delta;

namespace {

// §H.14.1: svDpiVersion lets C code determine the implementation's support
// for the standard -- this simulator reports itself an IEEE Std 1800
// implementation, whose users need not use the opaque handle types for
// every packed argument, where a simulator supporting only SV3.1a reports
// SV3.1a and its users shall.
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

// §H.14.1: with an IEEE Std 1800 implementation the SV3.1a-compatible
// semantics are available per function -- a declaration annotated "DPI"
// yields the SV3.1a argument passing semantics on the C side and one
// annotated "DPI-C" the IEEE Std 1800 semantics.
TEST(DpiCompatibility, TheSpecStringSelectsThePassingSemantics) {
  EXPECT_EQ(DpiPassingSemanticsOfSpecString("DPI"),
            DpiPackedArgPassing::kSv31aReference);
  EXPECT_EQ(DpiPassingSemanticsOfSpecString("DPI-C"),
            DpiPackedArgPassing::kCanonical);
}

// §H.14.1: svdpi.h may contain the SV3.1a definitions and prototypes and an
// IEEE Std 1800 implementation is not obligated to provide them; where the
// functionality is unsupported, DPI C code may not successfully bind.
TEST(DpiCompatibility, TheSv31aDefinitionsAreOptionalAndBindingMayFail) {
  EXPECT_FALSE(DpiSv31aDefinitionsAreObligatoryInSvdpiH());
  EXPECT_TRUE(DpiCCodeMayFailToBind(false));
  EXPECT_FALSE(DpiCCodeMayFailToBind(true));
}

// §H.14.1 under the run: a design declaring one import with "DPI" and one
// with "DPI-C" registers the first with the SV3.1a reference semantics and
// the second with the canonical ones, the choice being per declaration.
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
