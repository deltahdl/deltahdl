#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <initializer_list>

#include "helpers_mintymax.h"
namespace {

TEST(MinTypMaxDelays, SelectMin) {
  MinTypMax mtm{5, 10, 15};
  EXPECT_EQ(SelectMinTypMax(mtm, 0), 5u);
}

TEST(MinTypMaxDelays, SelectMax) {
  MinTypMax mtm{5, 10, 15};
  EXPECT_EQ(SelectMinTypMax(mtm, 2), 15u);
}

TEST(MinTypMaxDelays, NoRequiredOrdering) {
  MinTypMax mtm{20, 5, 10};
  EXPECT_EQ(SelectMinTypMax(mtm, 0), 20u);
  EXPECT_EQ(SelectMinTypMax(mtm, 1), 5u);
  EXPECT_EQ(SelectMinTypMax(mtm, 2), 10u);
}

}
