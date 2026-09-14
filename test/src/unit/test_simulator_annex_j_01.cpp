#include <gtest/gtest.h>

#include "simulator/foreign_code.h"

using namespace delta;

namespace {

// §J.1: Annex J describes common guidelines for the inclusion of foreign
// language code into a SystemVerilog application, with the intention of
// enabling the redistribution of C binaries in shared object form.
TEST(ForeignCodeGuidelines,
     TheyEnableRedistributionOfCBinariesAsSharedObjects) {
  EXPECT_EQ(ForeignCodeIntendedRedistributionForm(),
            ForeignCodeRedistributionForm::kSharedObject);
  EXPECT_NE(ForeignCodeIntendedRedistributionForm(),
            ForeignCodeRedistributionForm::kSourceCode);
  EXPECT_TRUE(ForeignCodeGuidelinesAreCommonToApplications());
}

}  // namespace
