// §28.16.1: min:typ:max delays

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <initializer_list>

#include "helpers_mintymax.h"
namespace {

// §28.16: "The strength of the input signal shall not affect the
//  propagation delay from an input to an output."
// (This is an architectural constraint, not directly testable via
//  the delay computation API — noted for completeness.)
// =============================================================
// §28.16.1: min:typ:max delays
// =============================================================
// §28.16.1: "The minimum, typical, and maximum values for each delay
//  shall be specified as expressions separated by colons."
// §28.16.1: "There shall be no required relation (e.g., min ≤ typ
//  ≤ max) between the expressions."
TEST(MinTypMaxDelays, SelectMin) {
  MinTypMax mtm{5, 10, 15};
  EXPECT_EQ(SelectMinTypMax(mtm, 0), 5u);
}

TEST(MinTypMaxDelays, SelectMax) {
  MinTypMax mtm{5, 10, 15};
  EXPECT_EQ(SelectMinTypMax(mtm, 2), 15u);
}

// §28.16.1: No required relation — max can be less than min.
TEST(MinTypMaxDelays, NoRequiredOrdering) {
  MinTypMax mtm{20, 5, 10};
  EXPECT_EQ(SelectMinTypMax(mtm, 0), 20u);
  EXPECT_EQ(SelectMinTypMax(mtm, 1), 5u);
  EXPECT_EQ(SelectMinTypMax(mtm, 2), 10u);
}

}  // namespace
