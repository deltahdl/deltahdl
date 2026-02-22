// §32.4: Mapping of SDF constructs to SystemVerilog

#include <gtest/gtest.h>
#include "simulation/sdf_parser.h"
#include "simulation/specify.h"

using namespace delta;

namespace {

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
  auto &checks = mgr.GetTimingChecks();
  EXPECT_EQ(checks[0].kind, TimingCheckKind::kSetup);
  EXPECT_EQ(checks[0].ref_signal, "clk");
  EXPECT_EQ(checks[0].limit, 50u);
}

}  // namespace
