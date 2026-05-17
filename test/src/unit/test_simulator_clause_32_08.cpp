#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

TEST(SdfParser, SdfDelayValueDefault) {
  SdfDelayValue dv;
  EXPECT_EQ(dv.min_val, 0u);
  EXPECT_EQ(dv.typ_val, 0u);
  EXPECT_EQ(dv.max_val, 0u);
}

TEST(SdfExpand, OneValueBroadcastsToAllTwelveSlots) {
  SdfDelayValue d;
  d.typ_val = 100;
  auto out = ExpandSdfDelays({d}, SdfMtm::kTypical);
  ASSERT_EQ(out.size(), 12u);
  for (auto v : out) EXPECT_EQ(v, 100u);
}

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

TEST(SdfExpand, TwelveValuesCopyDirectly) {
  std::vector<SdfDelayValue> vals(12);
  for (int i = 0; i < 12; ++i) vals[i].typ_val = (i + 1) * 7;
  auto out = ExpandSdfDelays(vals, SdfMtm::kTypical);
  ASSERT_EQ(out.size(), 12u);
  for (int i = 0; i < 12; ++i) EXPECT_EQ(out[i], (uint64_t)((i + 1) * 7));
}

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

TEST(SdfReduceToThree, XStateUsesTurnoffWhenTurnoffIsSmallest) {
  std::vector<SdfDelayValue> vals(4);
  vals[0].typ_val = 30;
  vals[1].typ_val = 20;
  vals[2].typ_val = 10;
  vals[3].typ_val = 99;
  auto out = ReduceSdfDelaysToThree(vals, SdfMtm::kTypical);
  EXPECT_EQ(out[0], 30u);
  EXPECT_EQ(out[1], 20u);
  EXPECT_EQ(out[2], 10u);
  EXPECT_EQ(out[3], 10u);
}

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
  EXPECT_EQ(out[3], 100u);
}

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
  EXPECT_EQ(got.delays[0], 7u);
  EXPECT_EQ(got.delays[1], 11u);
  EXPECT_EQ(got.delays[2], 7u);
  EXPECT_EQ(got.delays[3], 7u);
  EXPECT_EQ(got.delays[4], 11u);
  EXPECT_EQ(got.delays[5], 11u);
  EXPECT_EQ(got.delays[6], 7u);
  EXPECT_EQ(got.delays[7], 7u);
  EXPECT_EQ(got.delays[8], 11u);
  EXPECT_EQ(got.delays[9], 11u);
  EXPECT_EQ(got.delays[10], 11u);
  EXPECT_EQ(got.delays[11], 7u);
}

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
  EXPECT_EQ(pd.delays[0], 1u);
  EXPECT_EQ(pd.delays[1], 2u);
  EXPECT_EQ(pd.delays[2], 3u);
}

}
