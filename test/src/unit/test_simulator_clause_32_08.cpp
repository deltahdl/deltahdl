#include <gtest/gtest.h>

#include <vector>

#include "helpers_sdf_interconnect.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// Claim T (Table 32-4): "1 value" column broadcasts the single SDF value to
// every one of the 12 SystemVerilog transition slots.
TEST(SdfExpand, OneValueBroadcastsToAllTwelveSlots) {
  SdfDelayValue d;
  d.typ_val = 100;
  auto out = ExpandSdfDelays({d}, SdfMtm::kTypical);
  ASSERT_EQ(out.size(), 12u);
  for (auto v : out) EXPECT_EQ(v, 100u);
}

// Claim T (Table 32-4): "2 values" column, including the x->z = max(v1,v2) and
// z->x = min(v1,v2) derivations in the final two slots.
TEST(SdfExpand, TwoValuesSpreadAcrossRiseAndFallFamilies) {
  SdfDelayValue v1, v2;
  v1.typ_val = 10;
  v2.typ_val = 20;
  auto out = ExpandSdfDelays({v1, v2}, SdfMtm::kTypical);
  ASSERT_EQ(out.size(), 12u);
  EXPECT_EQ(out[0], 10u);
  EXPECT_EQ(out[1], 20u);
  EXPECT_EQ(out[2], 10u);
  EXPECT_EQ(out[3], 10u);
  EXPECT_EQ(out[4], 20u);
  EXPECT_EQ(out[5], 20u);
  EXPECT_EQ(out[6], 10u);
  EXPECT_EQ(out[7], 10u);
  EXPECT_EQ(out[8], 20u);
  EXPECT_EQ(out[9], 20u);
  EXPECT_EQ(out[10], 20u);
  EXPECT_EQ(out[11], 10u);
}

// Claim T (Table 32-4): "3 values" column, including the min/max combinations
// the table prescribes for the four x-state slots.
TEST(SdfExpand, ThreeValuesAddTurnoffAndDirectXSlots) {
  SdfDelayValue v1, v2, v3;
  v1.typ_val = 10;
  v2.typ_val = 20;
  v3.typ_val = 30;
  auto out = ExpandSdfDelays({v1, v2, v3}, SdfMtm::kTypical);
  ASSERT_EQ(out.size(), 12u);
  EXPECT_EQ(out[0], 10u);
  EXPECT_EQ(out[1], 20u);
  EXPECT_EQ(out[2], 30u);
  EXPECT_EQ(out[3], 10u);
  EXPECT_EQ(out[4], 30u);
  EXPECT_EQ(out[5], 20u);
  EXPECT_EQ(out[6], 10u);
  EXPECT_EQ(out[7], 30u);
  EXPECT_EQ(out[8], 20u);
  EXPECT_EQ(out[9], 20u);
  EXPECT_EQ(out[10], 30u);
  EXPECT_EQ(out[11], 10u);
}

// Claim T (Table 32-4): "6 values" column, where the six x-state slots are
// derived from min/max pairings of the six supplied values.
TEST(SdfExpand, SixValuesPopulateNonXSlotsAndDeriveXFromMinMax) {
  std::vector<SdfDelayValue> vals(6);
  for (int i = 0; i < 6; ++i) vals[i].typ_val = (i + 1) * 10;
  auto out = ExpandSdfDelays(vals, SdfMtm::kTypical);
  ASSERT_EQ(out.size(), 12u);
  EXPECT_EQ(out[0], 10u);
  EXPECT_EQ(out[1], 20u);
  EXPECT_EQ(out[2], 30u);
  EXPECT_EQ(out[3], 40u);
  EXPECT_EQ(out[4], 50u);
  EXPECT_EQ(out[5], 60u);
  EXPECT_EQ(out[6], 10u);
  EXPECT_EQ(out[7], 40u);
  EXPECT_EQ(out[8], 20u);
  EXPECT_EQ(out[9], 60u);
  EXPECT_EQ(out[10], 50u);
  EXPECT_EQ(out[11], 40u);
}

// Claim T (Table 32-4): "12 values" column copies all supplied values straight
// across with no derivation.
TEST(SdfExpand, TwelveValuesCopyDirectly) {
  std::vector<SdfDelayValue> vals(12);
  for (int i = 0; i < 12; ++i) vals[i].typ_val = (i + 1) * 7;
  auto out = ExpandSdfDelays(vals, SdfMtm::kTypical);
  ASSERT_EQ(out.size(), 12u);
  for (int i = 0; i < 12; ++i) EXPECT_EQ(out[i], (uint64_t)((i + 1) * 7));
}

// Claim R + Claim X (final paragraph): more than three SDF delays are reduced
// to three by ignoring the extras (the trailing 99s never appear), and the
// x-state delay is the minimum of the three retained values.
TEST(SdfReduceToThree, MoreThanThreeDropsExtrasAndDerivesXFromMin) {
  std::vector<SdfDelayValue> vals(6);
  vals[0].typ_val = 30;
  vals[1].typ_val = 10;
  vals[2].typ_val = 20;
  vals[3].typ_val = 99;
  vals[4].typ_val = 99;
  vals[5].typ_val = 99;
  auto out = ReduceSdfDelaysToThree(vals, SdfMtm::kTypical);
  EXPECT_EQ(out[0], 30u);
  EXPECT_EQ(out[1], 10u);
  EXPECT_EQ(out[2], 20u);
  EXPECT_EQ(out[3], 10u);
}

// Claim T applied by the production carrier: the annotator runs an IOPATH's
// three delay values through the Table 32-4 mapping and lands all 12 slots on
// the specify path delay.
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
  EXPECT_EQ(pd.delays[0], 10u);
  EXPECT_EQ(pd.delays[1], 20u);
  EXPECT_EQ(pd.delays[2], 30u);
  EXPECT_EQ(pd.delays[3], 10u);
  EXPECT_EQ(pd.delays[4], 30u);
  EXPECT_EQ(pd.delays[5], 20u);
  EXPECT_EQ(pd.delays[6], 10u);
  EXPECT_EQ(pd.delays[7], 30u);
  EXPECT_EQ(pd.delays[8], 20u);
  EXPECT_EQ(pd.delays[9], 20u);
  EXPECT_EQ(pd.delays[10], 30u);
  EXPECT_EQ(pd.delays[11], 10u);
}

// Claim T applied by the production carrier on the other construct §32.8 names
// (interconnect delays): a two-value INTERCONNECT is expanded to 12 slots.
TEST(SdfAnnotation, InterconnectTwoValuesPopulateXStateSlotsThroughAnnotator) {
  SpecifyManager mgr;
  ExpectTwoValueInterconnectExpansion(mgr, "a", "b", 7, 11);
}

}  // namespace
