// Tests for §32 — SDF backannotation parser and delay mapping.

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

// =============================================================================
// SDF file parsing
// =============================================================================

TEST(SdfParser, ParseEmptyFile) {
  SdfFile file;
  bool ok = ParseSdf("(DELAYFILE)", file);
  EXPECT_TRUE(ok);
  EXPECT_TRUE(file.cells.empty());
}

TEST(SdfParser, ParseVersion) {
  SdfFile file;
  bool ok = ParseSdf(R"((DELAYFILE (SDFVERSION "4.0")))", file);
  EXPECT_TRUE(ok);
  EXPECT_EQ(file.version, "4.0");
}

TEST(SdfParser, ParseDesign) {
  SdfFile file;
  bool ok = ParseSdf(R"((DELAYFILE (DESIGN "top")))", file);
  EXPECT_TRUE(ok);
  EXPECT_EQ(file.design, "top");
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
  auto& io = file.cells[0].iopaths[0];
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
  auto& io = file.cells[0].iopaths[0];
  EXPECT_EQ(io.fall.min_val, 4u);
  EXPECT_EQ(io.fall.typ_val, 5u);
  EXPECT_EQ(io.fall.max_val, 6u);
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

// =============================================================================
// SDF annotation to SpecifyManager
// =============================================================================

TEST(SdfParser, AnnotatePathDelays) {
  SdfFile file;
  SdfCell cell;
  cell.cell_type = "buf";
  cell.instance = "u1";
  SdfIopath io;
  io.src_port = "a";
  io.dst_port = "y";
  io.rise.typ_val = 100;
  io.fall.typ_val = 200;
  cell.iopaths.push_back(io);
  file.cells.push_back(cell);

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_TRUE(mgr.HasPathDelay("a", "y"));
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 100u);
}

TEST(SdfParser, AnnotateTimingChecks) {
  SdfFile file;
  SdfCell cell;
  cell.cell_type = "dff";
  cell.instance = "u2";
  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kSetup;
  tc.ref_port = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_port = "d";
  tc.limit.typ_val = 50;
  cell.timing_checks.push_back(tc);
  file.cells.push_back(cell);

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.TimingCheckCount(), 1u);
  auto& checks = mgr.GetTimingChecks();
  EXPECT_EQ(checks[0].kind, TimingCheckKind::kSetup);
  EXPECT_EQ(checks[0].ref_signal, "clk");
  EXPECT_EQ(checks[0].limit, 50u);
}

}  // namespace
