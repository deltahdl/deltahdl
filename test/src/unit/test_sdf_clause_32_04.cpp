// §32.4: Mapping of SDF constructs to SystemVerilog

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

TEST(SdfParser, SdfIopathEntry) {
  SdfIopath entry;
  entry.src_port = "a";
  entry.dst_port = "y";
  entry.rise.typ_val = 100;
  entry.fall.typ_val = 200;
  EXPECT_EQ(entry.src_port, "a");
  EXPECT_EQ(entry.rise.typ_val, 100u);
  EXPECT_EQ(entry.fall.typ_val, 200u);
}

TEST(SdfParser, SdfTimingCheckEntry) {
  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kSetup;
  tc.ref_port = "clk";
  tc.data_port = "d";
  tc.limit.typ_val = 50;
  EXPECT_EQ(tc.ref_port, "clk");
  EXPECT_EQ(tc.limit.typ_val, 50u);
}

TEST(SdfParser, SdfCellDefault) {
  SdfCell cell;
  EXPECT_TRUE(cell.cell_type.empty());
  EXPECT_TRUE(cell.instance.empty());
  EXPECT_TRUE(cell.iopaths.empty());
  EXPECT_TRUE(cell.timing_checks.empty());
}

TEST(SdfParser, ParseCellWithIopath) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (IOPATH a y (10) (20))
          )
        )
      )
    )
  )";
  bool ok = ParseSdf(sdf, file);
  EXPECT_TRUE(ok);
  ASSERT_EQ(file.cells.size(), 1u);
  EXPECT_EQ(file.cells[0].cell_type, "buf");
  EXPECT_EQ(file.cells[0].instance, "u1");
  ASSERT_EQ(file.cells[0].iopaths.size(), 1u);
}

TEST(SdfParser, ParseCellWithIopath_Ports) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (IOPATH a y (10) (20))
          )
        )
      )
    )
  )";
  ParseSdf(sdf, file);
  EXPECT_EQ(file.cells[0].iopaths[0].src_port, "a");
  EXPECT_EQ(file.cells[0].iopaths[0].dst_port, "y");
  EXPECT_EQ(file.cells[0].iopaths[0].rise.typ_val, 10u);
  EXPECT_EQ(file.cells[0].iopaths[0].fall.typ_val, 20u);
}

TEST(SdfParser, ParseTimingCheck) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "dff")
        (INSTANCE u2)
        (TIMINGCHECK
          (SETUP d (posedge clk) (5))
        )
      )
    )
  )";
  bool ok = ParseSdf(sdf, file);
  EXPECT_TRUE(ok);
  ASSERT_EQ(file.cells.size(), 1u);
  ASSERT_EQ(file.cells[0].timing_checks.size(), 1u);
}

TEST(SdfParser, ParseTimingCheck_Fields) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "dff")
        (INSTANCE u2)
        (TIMINGCHECK
          (SETUP d (posedge clk) (5))
        )
      )
    )
  )";
  ParseSdf(sdf, file);
  auto& tc = file.cells[0].timing_checks[0];
  EXPECT_EQ(tc.check_type, SdfCheckType::kSetup);
  EXPECT_EQ(tc.data_port, "d");
  EXPECT_EQ(tc.ref_port, "clk");
  EXPECT_EQ(tc.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.limit.typ_val, 5u);
}

TEST(SdfParser, ParseIncrementMode) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u4)
        (DELAY
          (INCREMENT
            (IOPATH a y (5) (10))
          )
        )
      )
    )
  )";
  bool ok = ParseSdf(sdf, file);
  EXPECT_TRUE(ok);
  ASSERT_EQ(file.cells[0].iopaths.size(), 1u);
  EXPECT_TRUE(file.cells[0].iopaths[0].is_increment);
}

TEST(SdfParser, ParseHoldCheck) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "dff")
        (INSTANCE u5)
        (TIMINGCHECK
          (HOLD d (posedge clk) (3))
        )
      )
    )
  )";
  bool ok = ParseSdf(sdf, file);
  EXPECT_TRUE(ok);
  auto& tc = file.cells[0].timing_checks[0];
  EXPECT_EQ(tc.check_type, SdfCheckType::kHold);
  EXPECT_EQ(tc.limit.typ_val, 3u);
}

TEST(SdfParser, ParseMultipleCells) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH a y (10) (20))))
      )
      (CELL
        (CELLTYPE "inv")
        (INSTANCE u2)
        (DELAY (ABSOLUTE (IOPATH a y (5) (8))))
      )
    )
  )";
  bool ok = ParseSdf(sdf, file);
  EXPECT_TRUE(ok);
  EXPECT_EQ(file.cells.size(), 2u);
  EXPECT_EQ(file.cells[0].instance, "u1");
  EXPECT_EQ(file.cells[1].instance, "u2");
}

}  // namespace
