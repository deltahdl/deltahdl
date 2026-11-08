#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

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
