#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_elaborator.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(TimescaleDirectiveElaboration,
     TimescaleSuppliesDefaultsToFollowingModule) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`timescale 10ns / 100ps\n"
      "module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* mod = FindModule(design, "m");
  ASSERT_NE(mod, nullptr);
  EXPECT_EQ(mod->timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(mod->timescale.magnitude, 10);
  EXPECT_EQ(mod->timescale.precision, TimeUnit::kPs);
  EXPECT_EQ(mod->timescale.prec_magnitude, 100);
}

TEST(TimescaleDirectiveElaboration,
     TimescaleSuppliesPrecisionWhenElementDeclaresOnlyUnit) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`timescale 1ns / 10ps\n"
      "module m;\n"
      "  timeunit 1us;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* mod = FindModule(design, "m");
  ASSERT_NE(mod, nullptr);
  EXPECT_EQ(mod->timescale.unit, TimeUnit::kUs);
  EXPECT_EQ(mod->timescale.magnitude, 1);
  EXPECT_EQ(mod->timescale.precision, TimeUnit::kPs);
  EXPECT_EQ(mod->timescale.prec_magnitude, 10);
}

TEST(TimescaleDirectiveElaboration,
     TimescaleSuppliesUnitWhenElementDeclaresOnlyPrecision) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`timescale 10us / 100ns\n"
      "module m;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* mod = FindModule(design, "m");
  ASSERT_NE(mod, nullptr);
  EXPECT_EQ(mod->timescale.unit, TimeUnit::kUs);
  EXPECT_EQ(mod->timescale.magnitude, 10);
  EXPECT_EQ(mod->timescale.precision, TimeUnit::kPs);
  EXPECT_EQ(mod->timescale.prec_magnitude, 1);
}

}  // namespace
