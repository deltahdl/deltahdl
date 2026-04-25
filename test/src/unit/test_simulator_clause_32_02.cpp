#include <gtest/gtest.h>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// §32.2 names four categories of timing values that SDF backannotation
// updates: specify path delays, specparam values, timing check constraint
// values, and interconnect delays. The tests below pin the backannotation
// entry point to all four.

TEST(SdfBackannotation, UpdatesSpecifyPathDelays) {
  SdfFile file;
  SdfCell cell;
  SdfIopath io;
  io.src_port = "a";
  io.dst_port = "y";
  io.rise.typ_val = 7;
  io.fall.typ_val = 11;
  cell.iopaths.push_back(io);
  file.cells.push_back(cell);

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_TRUE(mgr.HasPathDelay("a", "y"));
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 7u);
}

TEST(SdfBackannotation, UpdatesSpecparamValues) {
  SdfFile file;
  SdfCell cell;
  SdfSpecparam sp;
  sp.name = "tRise";
  sp.value.min_val = 1;
  sp.value.typ_val = 2;
  sp.value.max_val = 3;
  cell.specparams.push_back(sp);
  file.cells.push_back(cell);

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetSpecparamValues().size(), 1u);
  EXPECT_EQ(mgr.GetSpecparamValues()[0].name, "tRise");
  EXPECT_EQ(mgr.GetSpecparamValues()[0].value, 2u);
}

TEST(SdfBackannotation, UpdatesTimingCheckConstraints) {
  SdfFile file;
  SdfCell cell;
  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kSetup;
  tc.ref_port = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_port = "d";
  tc.limit.typ_val = 13;
  cell.timing_checks.push_back(tc);
  file.cells.push_back(cell);

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.TimingCheckCount(), 1u);
  EXPECT_EQ(mgr.GetTimingChecks()[0].limit, 13u);
}

TEST(SdfBackannotation, UpdatesInterconnectDelays) {
  SdfFile file;
  SdfCell cell;
  SdfInterconnect ic;
  ic.src_port = "u1.q";
  ic.dst_port = "u2.d";
  ic.rise.typ_val = 4;
  ic.fall.typ_val = 9;
  cell.interconnects.push_back(ic);
  file.cells.push_back(cell);

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  const auto& got = mgr.GetInterconnectDelays()[0];
  EXPECT_EQ(got.src_port, "u1.q");
  EXPECT_EQ(got.dst_port, "u2.d");
  EXPECT_EQ(got.rise, 4u);
  EXPECT_EQ(got.fall, 9u);
}

// §32.2 also says that timing values from SDF "update" — i.e. the selected
// MTM column applies uniformly to every category named in the clause.
TEST(SdfBackannotation, MtmSelectionAppliesToAllCategories) {
  SdfFile file;
  SdfCell cell;

  SdfIopath io;
  io.src_port = "a";
  io.dst_port = "y";
  io.rise = {1, 2, 3};
  io.fall = {1, 2, 3};
  cell.iopaths.push_back(io);

  SdfSpecparam sp;
  sp.name = "tHold";
  sp.value = {10, 20, 30};
  cell.specparams.push_back(sp);

  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kSetup;
  tc.ref_port = "clk";
  tc.data_port = "d";
  tc.limit = {100, 200, 300};
  cell.timing_checks.push_back(tc);

  SdfInterconnect ic;
  ic.src_port = "p";
  ic.dst_port = "q";
  ic.rise = {1000, 2000, 3000};
  ic.fall = {1000, 2000, 3000};
  cell.interconnects.push_back(ic);

  file.cells.push_back(cell);

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kMaximum);

  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 3u);
  ASSERT_EQ(mgr.GetSpecparamValues().size(), 1u);
  EXPECT_EQ(mgr.GetSpecparamValues()[0].value, 30u);
  ASSERT_EQ(mgr.TimingCheckCount(), 1u);
  EXPECT_EQ(mgr.GetTimingChecks()[0].limit, 300u);
  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  EXPECT_EQ(mgr.GetInterconnectDelays()[0].rise, 3000u);
  EXPECT_EQ(mgr.GetInterconnectDelays()[0].fall, 3000u);
}

// §32.2: "Any SystemVerilog timing value for which the SDF file does not
// provide a value shall not be modified" is a §32.3 statement, but the
// converse — that backannotation only writes the four named categories and
// leaves SpecifyManager untouched when an SDF cell carries none of them —
// is implicit in §32.2's definition of what backannotation is.
TEST(SdfBackannotation, EmptyCellLeavesManagerUntouched) {
  SdfFile file;
  file.cells.push_back(SdfCell{});

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_EQ(mgr.PathDelayCount(), 0u);
  EXPECT_EQ(mgr.TimingCheckCount(), 0u);
  EXPECT_TRUE(mgr.GetSpecparamValues().empty());
  EXPECT_TRUE(mgr.GetInterconnectDelays().empty());
}

// Edge case: a file with no cells at all. §32.2 defines backannotation as
// applying values "from the SDF file" — with zero cells, the update set is
// empty and the manager stays at its prebackannotation state.
TEST(SdfBackannotation, EmptyFileProducesNoUpdates) {
  SdfFile file;

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_EQ(mgr.PathDelayCount(), 0u);
  EXPECT_EQ(mgr.TimingCheckCount(), 0u);
  EXPECT_TRUE(mgr.GetSpecparamValues().empty());
  EXPECT_TRUE(mgr.GetInterconnectDelays().empty());
}

// Edge case: the cell list is iterated in full. With two cells carrying
// non-overlapping timing content, both contributions appear on the manager.
TEST(SdfBackannotation, MultipleCellsAllContribute) {
  SdfFile file;

  SdfCell cell_a;
  SdfIopath io;
  io.src_port = "a";
  io.dst_port = "y";
  io.rise.typ_val = 4;
  io.fall.typ_val = 8;
  cell_a.iopaths.push_back(io);
  file.cells.push_back(cell_a);

  SdfCell cell_b;
  SdfInterconnect ic;
  ic.src_port = "u1.q";
  ic.dst_port = "u2.d";
  ic.rise.typ_val = 3;
  ic.fall.typ_val = 5;
  cell_b.interconnects.push_back(ic);
  file.cells.push_back(cell_b);

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_TRUE(mgr.HasPathDelay("a", "y"));
  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  EXPECT_EQ(mgr.GetInterconnectDelays()[0].src_port, "u1.q");
}

// Edge case: several entries of the same category inside a single cell are
// each applied. Backannotation is not limited to one update per category
// per cell — every value in the SDF file reaches the manager.
TEST(SdfBackannotation, MultipleEntriesPerCategoryApplied) {
  SdfFile file;
  SdfCell cell;

  SdfIopath io1;
  io1.src_port = "a";
  io1.dst_port = "y";
  io1.rise.typ_val = 2;
  cell.iopaths.push_back(io1);

  SdfIopath io2;
  io2.src_port = "b";
  io2.dst_port = "z";
  io2.rise.typ_val = 6;
  cell.iopaths.push_back(io2);

  SdfInterconnect ic1;
  ic1.src_port = "p1";
  ic1.dst_port = "q1";
  ic1.rise.typ_val = 11;
  cell.interconnects.push_back(ic1);

  SdfInterconnect ic2;
  ic2.src_port = "p2";
  ic2.dst_port = "q2";
  ic2.rise.typ_val = 13;
  cell.interconnects.push_back(ic2);

  file.cells.push_back(cell);

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_EQ(mgr.PathDelayCount(), 2u);
  EXPECT_TRUE(mgr.HasPathDelay("a", "y"));
  EXPECT_TRUE(mgr.HasPathDelay("b", "z"));
  EXPECT_EQ(mgr.GetInterconnectDelays().size(), 2u);
}

}  // namespace
