#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// =============================================================================
// §32.8 sentences 1-4 + Table 32-4: SDF-to-SystemVerilog delay value mapping
// =============================================================================

TEST(SdfParser, SdfDelayValueDefault) {
  SdfDelayValue dv;
  EXPECT_EQ(dv.min_val, 0u);
  EXPECT_EQ(dv.typ_val, 0u);
  EXPECT_EQ(dv.max_val, 0u);
}

// Table 32-4 column "1 value": every SystemVerilog transition collapses onto v1.
TEST(SdfExpand, OneValueBroadcastsToAllTwelveSlots) {
  SdfDelayValue d;
  d.typ_val = 100;
  auto out = ExpandSdfDelays({d}, SdfMtm::kTypical);
  ASSERT_EQ(out.size(), 12u);
  for (auto v : out) EXPECT_EQ(v, 100u);
}

// Table 32-4 column "2 values": v1 covers the rise-family transitions
// (0->1, 0->z, z->1) and v2 covers the fall-family ones (1->0, 1->z, z->0).
// The X-state slots collapse to the matching family value, except x->z and
// z->x which use max/min across v1 and v2.
TEST(SdfExpand, TwoValuesSpreadAcrossRiseAndFallFamilies) {
  SdfDelayValue v1, v2;
  v1.typ_val = 10;
  v2.typ_val = 20;
  auto out = ExpandSdfDelays({v1, v2}, SdfMtm::kTypical);
  ASSERT_EQ(out.size(), 12u);
  EXPECT_EQ(out[0], 10u);              // 0->1 = v1
  EXPECT_EQ(out[1], 20u);              // 1->0 = v2
  EXPECT_EQ(out[2], 10u);              // 0->z = v1
  EXPECT_EQ(out[3], 10u);              // z->1 = v1
  EXPECT_EQ(out[4], 20u);              // 1->z = v2
  EXPECT_EQ(out[5], 20u);              // z->0 = v2
  EXPECT_EQ(out[6], 10u);              // 0->x = v1
  EXPECT_EQ(out[7], 10u);              // x->1 = v1
  EXPECT_EQ(out[8], 20u);              // 1->x = v2
  EXPECT_EQ(out[9], 20u);              // x->0 = v2
  EXPECT_EQ(out[10], 20u);             // x->z = max(v1,v2)
  EXPECT_EQ(out[11], 10u);             // z->x = min(v1,v2)
}

// Table 32-4 column "3 values": v3 covers the to-z direction. The x->0,
// x->z, z->x slots are not derived from the §30.5.1 pessimistic min/max
// rule — Table 32-4 fixes them to v2, v3, min(v1,v2) respectively.
TEST(SdfExpand, ThreeValuesAddTurnoffAndDirectXSlots) {
  SdfDelayValue v1, v2, v3;
  v1.typ_val = 10;
  v2.typ_val = 20;
  v3.typ_val = 30;
  auto out = ExpandSdfDelays({v1, v2, v3}, SdfMtm::kTypical);
  ASSERT_EQ(out.size(), 12u);
  EXPECT_EQ(out[0], 10u);              // 0->1 = v1
  EXPECT_EQ(out[1], 20u);              // 1->0 = v2
  EXPECT_EQ(out[2], 30u);              // 0->z = v3
  EXPECT_EQ(out[3], 10u);              // z->1 = v1
  EXPECT_EQ(out[4], 30u);              // 1->z = v3
  EXPECT_EQ(out[5], 20u);              // z->0 = v2
  EXPECT_EQ(out[6], 10u);              // 0->x = min(v1,v3)
  EXPECT_EQ(out[7], 30u);              // x->1 = max(v1,v3)
  EXPECT_EQ(out[8], 20u);              // 1->x = min(v2,v3)
  EXPECT_EQ(out[9], 20u);              // x->0 = v2
  EXPECT_EQ(out[10], 30u);             // x->z = v3
  EXPECT_EQ(out[11], 10u);             // z->x = min(v1,v2)
}

// Table 32-4 column "6 values": v1..v6 land on the six non-x transitions
// directly; the six x-transition slots are derived from min/max of the
// neighbouring non-x slots per the table.
TEST(SdfExpand, SixValuesPopulateNonXSlotsAndDeriveXFromMinMax) {
  std::vector<SdfDelayValue> vals(6);
  for (int i = 0; i < 6; ++i) vals[i].typ_val = (i + 1) * 10;
  auto out = ExpandSdfDelays(vals, SdfMtm::kTypical);
  ASSERT_EQ(out.size(), 12u);
  EXPECT_EQ(out[0], 10u);              // 0->1 = v1
  EXPECT_EQ(out[1], 20u);              // 1->0 = v2
  EXPECT_EQ(out[2], 30u);              // 0->z = v3
  EXPECT_EQ(out[3], 40u);              // z->1 = v4
  EXPECT_EQ(out[4], 50u);              // 1->z = v5
  EXPECT_EQ(out[5], 60u);              // z->0 = v6
  EXPECT_EQ(out[6], 10u);              // 0->x = min(v1,v3)
  EXPECT_EQ(out[7], 40u);              // x->1 = max(v1,v4)
  EXPECT_EQ(out[8], 20u);              // 1->x = min(v2,v5)
  EXPECT_EQ(out[9], 60u);              // x->0 = max(v2,v6)
  EXPECT_EQ(out[10], 50u);             // x->z = max(v3,v5)
  EXPECT_EQ(out[11], 40u);             // z->x = min(v4,v6)
}

// Table 32-4 column "12 values": every SystemVerilog transition slot maps
// directly to its matching SDF value; no derivation is performed.
TEST(SdfExpand, TwelveValuesCopyDirectly) {
  std::vector<SdfDelayValue> vals(12);
  for (int i = 0; i < 12; ++i) vals[i].typ_val = (i + 1) * 7;
  auto out = ExpandSdfDelays(vals, SdfMtm::kTypical);
  ASSERT_EQ(out.size(), 12u);
  for (int i = 0; i < 12; ++i) EXPECT_EQ(out[i], (uint64_t)((i + 1) * 7));
}

// MTM selection threads through the 12-slot expansion: kMinimum picks
// every value's min_val, kMaximum picks max_val.
TEST(SdfExpand, MtmSelectMinimumThroughExpansion) {
  SdfDelayValue v1;
  v1.min_val = 5;
  v1.typ_val = 10;
  v1.max_val = 15;
  auto out = ExpandSdfDelays({v1}, SdfMtm::kMinimum);
  EXPECT_EQ(out[0], 5u);
  EXPECT_EQ(out[6], 5u);
}

TEST(SdfExpand, MtmSelectMaximumThroughExpansion) {
  SdfDelayValue v1;
  v1.min_val = 5;
  v1.typ_val = 10;
  v1.max_val = 15;
  auto out = ExpandSdfDelays({v1}, SdfMtm::kMaximum);
  EXPECT_EQ(out[0], 15u);
  EXPECT_EQ(out[11], 15u);
}

TEST(SdfExpand, EmptyInputProducesZeroes) {
  auto out = ExpandSdfDelays({}, SdfMtm::kTypical);
  ASSERT_EQ(out.size(), 12u);
  for (auto v : out) EXPECT_EQ(v, 0u);
}

// =============================================================================
// §32.8 sentences 5-7: "other delays" reduction with X-state = min
// =============================================================================

// §32.8: more than three SDF delays are reduced to three SystemVerilog
// delays by simply ignoring the extras. v4 onward must drop out and the
// X-state delay must equal the minimum of the surviving three.
TEST(SdfReduceToThree, MoreThanThreeDropsExtrasAndDerivesXFromMin) {
  std::vector<SdfDelayValue> vals(6);
  vals[0].typ_val = 30;
  vals[1].typ_val = 10;
  vals[2].typ_val = 20;
  vals[3].typ_val = 99;  // ignored by §32.8
  vals[4].typ_val = 99;
  vals[5].typ_val = 99;
  auto out = ReduceSdfDelaysToThree(vals, SdfMtm::kTypical);
  EXPECT_EQ(out[0], 30u);             // rise = v1
  EXPECT_EQ(out[1], 10u);             // fall = v2
  EXPECT_EQ(out[2], 20u);             // turnoff = v3
  EXPECT_EQ(out[3], 10u);             // x = min(v1,v2,v3) = 10
}

// The X-state minimum must consider the turnoff slot, not just the rise
// and fall slots. A bug that compared only two of the three would pass the
// other tests (where v1 or v2 is smallest) but miss the case where the
// smallest delay belongs to v3.
TEST(SdfReduceToThree, XStateUsesTurnoffWhenTurnoffIsSmallest) {
  std::vector<SdfDelayValue> vals(4);
  vals[0].typ_val = 30;
  vals[1].typ_val = 20;
  vals[2].typ_val = 10;  // turnoff is the smallest
  vals[3].typ_val = 99;  // ignored
  auto out = ReduceSdfDelaysToThree(vals, SdfMtm::kTypical);
  EXPECT_EQ(out[0], 30u);
  EXPECT_EQ(out[1], 20u);
  EXPECT_EQ(out[2], 10u);
  EXPECT_EQ(out[3], 10u);             // x = min(v1,v2,v3) = v3
}

// MTM selection threads through the reduction.
TEST(SdfReduceToThree, MtmSelectionAppliesPerValue) {
  std::vector<SdfDelayValue> vals(4);
  vals[0].min_val = 1;
  vals[0].typ_val = 10;
  vals[0].max_val = 100;
  vals[1].min_val = 2;
  vals[1].typ_val = 20;
  vals[1].max_val = 200;
  vals[2].min_val = 3;
  vals[2].typ_val = 30;
  vals[2].max_val = 300;
  vals[3].min_val = 999;
  vals[3].typ_val = 999;
  vals[3].max_val = 999;
  auto out = ReduceSdfDelaysToThree(vals, SdfMtm::kMaximum);
  EXPECT_EQ(out[0], 100u);
  EXPECT_EQ(out[1], 200u);
  EXPECT_EQ(out[2], 300u);
  EXPECT_EQ(out[3], 100u);            // min of 100/200/300
}

// =============================================================================
// Production wiring: AnnotateSdfToManager applies Table 32-4 to PathDelay
// =============================================================================

// §32.8 sentence 1 + Table 32-4 col "3 values": after annotation the
// PathDelay carries all twelve transition slots populated according to
// Table 32-4 — not just the rise/fall/turnoff slots. The IOPATH path in
// the SDF flow is the production consumer that must apply the §32.8
// expansion (the parser models exactly three SDF delays per IOPATH).
TEST(SdfAnnotation, IopathExpansionPopulatesAllTwelveTransitionSlots) {
  SdfFile file;
  SdfCell cell;
  SdfIopath io;
  io.src_port = "a";
  io.dst_port = "z";
  io.rise.typ_val = 10;
  io.fall.typ_val = 20;
  io.turnoff.typ_val = 30;
  cell.iopaths.push_back(io);
  file.cells.push_back(cell);

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 10u);              // 0->1 = v1
  EXPECT_EQ(pd.delays[1], 20u);              // 1->0 = v2
  EXPECT_EQ(pd.delays[2], 30u);              // 0->z = v3
  EXPECT_EQ(pd.delays[3], 10u);              // z->1 = v1 (was 0 pre-§32.8)
  EXPECT_EQ(pd.delays[4], 30u);              // 1->z = v3 (was 0 pre-§32.8)
  EXPECT_EQ(pd.delays[5], 20u);              // z->0 = v2 (was 0 pre-§32.8)
  EXPECT_EQ(pd.delays[6], 10u);              // 0->x = min(v1,v3)
  EXPECT_EQ(pd.delays[7], 30u);              // x->1 = max(v1,v3)
  EXPECT_EQ(pd.delays[8], 20u);              // 1->x = min(v2,v3)
  EXPECT_EQ(pd.delays[9], 20u);              // x->0 = v2
  EXPECT_EQ(pd.delays[10], 30u);             // x->z = v3
  EXPECT_EQ(pd.delays[11], 10u);             // z->x = min(v1,v2)
}

// §32.8 sentence 1 + Table 32-4 col "2 values": two-value SDF interconnect
// follows the table — including the x->z = max(v1,v2) and z->x = min(v1,v2)
// derivations which differ from the §30.5.1 pessimistic min/max rule.
TEST(SdfAnnotation, InterconnectTwoValuesPopulateXStateSlotsThroughAnnotator) {
  SdfFile file;
  SdfCell cell;
  SdfInterconnect ic;
  ic.kind = SdfInterconnectKind::kInterconnect;
  ic.src_port = "a";
  ic.dst_port = "b";
  ic.rise.typ_val = 7;
  ic.fall.typ_val = 11;
  cell.interconnects.push_back(ic);
  file.cells.push_back(cell);

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  const auto& got = mgr.GetInterconnectDelays()[0];
  EXPECT_EQ(got.delays[0], 7u);              // 0->1 = v1
  EXPECT_EQ(got.delays[1], 11u);             // 1->0 = v2
  EXPECT_EQ(got.delays[2], 7u);              // 0->z = v1
  EXPECT_EQ(got.delays[3], 7u);              // z->1 = v1
  EXPECT_EQ(got.delays[4], 11u);             // 1->z = v2
  EXPECT_EQ(got.delays[5], 11u);             // z->0 = v2
  EXPECT_EQ(got.delays[6], 7u);              // 0->x = v1
  EXPECT_EQ(got.delays[7], 7u);              // x->1 = v1
  EXPECT_EQ(got.delays[8], 11u);             // 1->x = v2
  EXPECT_EQ(got.delays[9], 11u);             // x->0 = v2
  EXPECT_EQ(got.delays[10], 11u);            // x->z = max(v1,v2)
  EXPECT_EQ(got.delays[11], 7u);             // z->x = min(v1,v2)
}

// The IOPath production wiring must forward the caller-supplied MTM mode
// into ExpandSdfDelays so that a kMinimum/kMaximum invocation observes
// each value's min_val/max_val rather than collapsing onto typ_val. A
// regression that hardcoded kTypical or dropped the parameter would still
// satisfy the helper-level MTM tests but fail here because the integration
// path actually consumes the SdfDelayValue's three fields.
TEST(SdfAnnotation, IopathExpansionRespectsMtmSelection) {
  SdfFile file;
  SdfCell cell;
  SdfIopath io;
  io.src_port = "a";
  io.dst_port = "z";
  io.rise.min_val = 1;
  io.rise.typ_val = 10;
  io.rise.max_val = 100;
  io.fall.min_val = 2;
  io.fall.typ_val = 20;
  io.fall.max_val = 200;
  io.turnoff.min_val = 3;
  io.turnoff.typ_val = 30;
  io.turnoff.max_val = 300;
  cell.iopaths.push_back(io);
  file.cells.push_back(cell);

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kMinimum);
  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 1u);              // 0->1 = rise.min
  EXPECT_EQ(pd.delays[1], 2u);              // 1->0 = fall.min
  EXPECT_EQ(pd.delays[2], 3u);              // 0->z = turnoff.min
}

}  // namespace
