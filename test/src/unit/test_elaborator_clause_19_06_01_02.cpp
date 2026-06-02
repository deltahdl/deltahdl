#include <gtest/gtest.h>

#include "elaborator/cross_bin_with_covergroup.h"

using namespace delta;

namespace {

// When a cross_identifier is used as a select_expression, only the
// cross_identifier of the enclosing cross may be used; any other cross_identifier
// shall be disallowed (LRM 19.6.1.2).
TEST(CrossBinWithCovergroup, OnlyEnclosingCrossIdentifierIsLegal) {
  EXPECT_TRUE(CrossIdentifierSelectIsLegal("X", "X"));
  EXPECT_FALSE(CrossIdentifierSelectIsLegal("Y", "X"));
}

// The integer_covergroup_expression of a matches clause shall evaluate to a
// positive integer; zero or a negative value is illegal (LRM 19.6.1.2).
TEST(CrossBinWithCovergroup, MatchesCountShallBePositive) {
  EXPECT_TRUE(CrossMatchesCountIsLegal(1));
  EXPECT_TRUE(CrossMatchesCountIsLegal(127));
  EXPECT_FALSE(CrossMatchesCountIsLegal(0));
  EXPECT_FALSE(CrossMatchesCountIsLegal(-3));
}

}  // namespace
