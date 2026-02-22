// §32.8: SDF to SystemVerilog delay value mapping

#include "simulation/sdf_parser.h"
#include "simulation/specify.h"
#include <gtest/gtest.h>

using namespace delta;

namespace {

// =============================================================================
// SDF delay value expansion (Table 32-4)
// =============================================================================
TEST(SdfParser, ExpandOneDelay) {
  SdfDelayValue d;
  d.typ_val = 100;
  auto expanded = ExpandSdfDelays({d}, SdfMtm::kTypical);
  ASSERT_EQ(expanded.size(), 12u);
  for (auto v : expanded)
    EXPECT_EQ(v, 100u);
}

TEST(SdfParser, ExpandTwoDelays) {
  SdfDelayValue rise, fall;
  rise.typ_val = 10;
  fall.typ_val = 20;
  auto expanded = ExpandSdfDelays({rise, fall}, SdfMtm::kTypical);
  // 2-value: rise, fall -> rise used for positive, fall for negative
  EXPECT_EQ(expanded[0], 10u); // 0->1
  EXPECT_EQ(expanded[1], 20u); // 1->0
}

TEST(SdfParser, ExpandThreeDelays) {
  SdfDelayValue rise, fall, turnoff;
  rise.typ_val = 10;
  fall.typ_val = 20;
  turnoff.typ_val = 30;
  auto expanded = ExpandSdfDelays({rise, fall, turnoff}, SdfMtm::kTypical);
  EXPECT_EQ(expanded[0], 10u); // 0->1
  EXPECT_EQ(expanded[1], 20u); // 1->0
  EXPECT_EQ(expanded[2], 30u); // 0->z
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

TEST(SdfParser, ParseMinTypMaxDelay) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "inv")
        (INSTANCE u3)
        (DELAY
          (ABSOLUTE
            (IOPATH a y (1:2:3) (4:5:6))
          )
        )
      )
    )
  )";
  bool ok = ParseSdf(sdf, file);
  EXPECT_TRUE(ok);
  ASSERT_EQ(file.cells[0].iopaths.size(), 1u);
}

TEST(SdfParser, ParseMinTypMaxDelay_RiseValues) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "inv")
        (INSTANCE u3)
        (DELAY
          (ABSOLUTE
            (IOPATH a y (1:2:3) (4:5:6))
          )
        )
      )
    )
  )";
  ParseSdf(sdf, file);
  auto &io = file.cells[0].iopaths[0];
  EXPECT_EQ(io.rise.min_val, 1u);
  EXPECT_EQ(io.rise.typ_val, 2u);
  EXPECT_EQ(io.rise.max_val, 3u);
}

TEST(SdfParser, ParseMinTypMaxDelay_FallValues) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "inv")
        (INSTANCE u3)
        (DELAY
          (ABSOLUTE
            (IOPATH a y (1:2:3) (4:5:6))
          )
        )
      )
    )
  )";
  ParseSdf(sdf, file);
  auto &io = file.cells[0].iopaths[0];
  EXPECT_EQ(io.fall.min_val, 4u);
  EXPECT_EQ(io.fall.typ_val, 5u);
  EXPECT_EQ(io.fall.max_val, 6u);
}

} // namespace
