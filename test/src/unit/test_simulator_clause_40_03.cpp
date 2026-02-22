// §40.3: SystemVerilog real-time coverage access

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "simulation/dpi_runtime.h"

using namespace delta;

namespace {

// =============================================================================
// S40: Coverage API
// =============================================================================
TEST(Api, CoverageControlStartStop) {
  CoverageApi cov;
  EXPECT_EQ(cov.GetControl(), CoverageControl::kStart);  // Default.

  cov.SetControl(CoverageControl::kStop);
  EXPECT_EQ(cov.GetControl(), CoverageControl::kStop);

  cov.SetControl(CoverageControl::kReset);
  EXPECT_EQ(cov.GetControl(), CoverageControl::kReset);
}

TEST(Api, CoverageGetMaxBins) {
  CoverageApi cov;
  EXPECT_EQ(cov.GetMaxBins(), 64u);  // Default.

  cov.SetMaxBins(128);
  EXPECT_EQ(cov.GetMaxBins(), 128u);
}

TEST(Api, CoverageActiveState) {
  CoverageApi cov;
  EXPECT_TRUE(cov.IsActive());  // Default.

  cov.SetActive(false);
  EXPECT_FALSE(cov.IsActive());
}

TEST(Api, CoverageDbAccess) {
  CoverageApi cov;
  cov.StoreValue("cg.cp.coverage", 75.0);
  EXPECT_DOUBLE_EQ(cov.GetValue("cg.cp.coverage"), 75.0);

  // Missing key returns 0.
  EXPECT_DOUBLE_EQ(cov.GetValue("nonexistent"), 0.0);
}

}  // namespace
