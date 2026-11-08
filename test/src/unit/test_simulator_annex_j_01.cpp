#include <gtest/gtest.h>

#include "simulator/foreign_code.h"

using namespace delta;

namespace {

TEST(ForeignCodeGuidelines,
     TheyEnableRedistributionOfCBinariesAsSharedObjects) {
  EXPECT_EQ(ForeignCodeIntendedRedistributionForm(),
            ForeignCodeRedistributionForm::kSharedObject);
  EXPECT_NE(ForeignCodeIntendedRedistributionForm(),
            ForeignCodeRedistributionForm::kSourceCode);
  EXPECT_TRUE(ForeignCodeGuidelinesAreCommonToApplications());
}

}  // namespace
