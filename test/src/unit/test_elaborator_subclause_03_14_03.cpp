#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §3.14.3 (printed page 61): the global precision is the finest precision of
// every `timescale in the design, so the 1 fs one before the package counts
// even though the module's header is under 1 ns. ComputeGlobalTimePrecision
// reads it from the compilation unit's preproc_global_precision; the fixture
// left that unset, and counted only the directive at the module's header.
TEST(GlobalTimePrecisionElaboration, FinerTimescaleBeforePackageCounts) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`timescale 1ns / 1fs\n"
      "package p;\n"
      "endpackage\n"
      "`timescale 1ns / 1ns\n"
      "module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->global_time_precision, TimeUnit::kFs);
}

}  // namespace
