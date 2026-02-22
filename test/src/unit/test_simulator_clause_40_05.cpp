// §40.5: VPI coverage extensions

#include "vpi/sv_vpi_user.h"
#include <gtest/gtest.h>

namespace {

// =============================================================================
// Coverage VPI constants
// =============================================================================
TEST(SvVpiUser, CoverageControlConstants) {
  EXPECT_EQ(vpiCoverageStart, 750);
  EXPECT_EQ(vpiCoverageStop, 751);
  EXPECT_EQ(vpiCoverageReset, 752);
  EXPECT_EQ(vpiCoverageCheck, 753);
}

TEST(SvVpiUser, CoverageTypeConstants) {
  EXPECT_EQ(vpiAssertCoverage, 760);
  EXPECT_EQ(vpiStatementCoverage, 762);
  EXPECT_EQ(vpiToggleCoverage, 763);
  EXPECT_EQ(vpiCovered, 765);
}

} // namespace
