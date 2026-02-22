// §32.8: SDF to SystemVerilog delay value mapping

#include <gtest/gtest.h>
#include "simulation/sdf_parser.h"
#include "simulation/specify.h"

using namespace delta;

namespace {

// =============================================================================
// SDF data structures
// =============================================================================
TEST(SdfParser, SdfDelayValueDefault) {
  SdfDelayValue dv;
  EXPECT_EQ(dv.min_val, 0u);
  EXPECT_EQ(dv.typ_val, 0u);
  EXPECT_EQ(dv.max_val, 0u);
}

// =============================================================================
// SDF delay value expansion (Table 32-4)
// =============================================================================
TEST(SdfParser, ExpandOneDelay) {
  SdfDelayValue d;
  d.typ_val = 100;
  auto expanded = ExpandSdfDelays({d}, SdfMtm::kTypical);
  ASSERT_EQ(expanded.size(), 12u);
  for (auto v : expanded) EXPECT_EQ(v, 100u);
}

TEST(SdfParser, ExpandTwoDelays) {
  SdfDelayValue rise, fall;
  rise.typ_val = 10;
  fall.typ_val = 20;
  auto expanded = ExpandSdfDelays({rise, fall}, SdfMtm::kTypical);
  // 2-value: rise, fall -> rise used for positive, fall for negative
  EXPECT_EQ(expanded[0], 10u);  // 0->1
  EXPECT_EQ(expanded[1], 20u);  // 1->0
}

TEST(SdfParser, ExpandThreeDelays) {
  SdfDelayValue rise, fall, turnoff;
  rise.typ_val = 10;
  fall.typ_val = 20;
  turnoff.typ_val = 30;
  auto expanded = ExpandSdfDelays({rise, fall, turnoff}, SdfMtm::kTypical);
  EXPECT_EQ(expanded[0], 10u);  // 0->1
  EXPECT_EQ(expanded[1], 20u);  // 1->0
  EXPECT_EQ(expanded[2], 30u);  // 0->z
}

TEST(SdfParser, MtmSelectMinimum) {
  SdfDelayValue d;
  d.min_val = 5;
  d.typ_val = 10;
  d.max_val = 15;
  auto expanded = ExpandSdfDelays({d}, SdfMtm::kMinimum);
  EXPECT_EQ(expanded[0], 5u);
}

TEST(SdfParser, MtmSelectMaximum) {
  SdfDelayValue d;
  d.min_val = 5;
  d.typ_val = 10;
  d.max_val = 15;
  auto expanded = ExpandSdfDelays({d}, SdfMtm::kMaximum);
  EXPECT_EQ(expanded[0], 15u);
}

}  // namespace
