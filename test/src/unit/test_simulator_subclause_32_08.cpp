#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_sdf_design.h"
#include "fixture_simulator.h"
#include "fixture_specify_manager.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// §32.8 is a rule about how many delay values an SDF entry supplied and what
// the construct it reaches can hold, so both halves have to be produced rather
// than assembled. The SystemVerilog half is built from real source: a module
// path declaration (§30.5.1) is the construct that carries twelve state
// transition delays, and a gate primitive's propagation delay (§28.16) is the
// construct that carries three. The SDF half is real SDF text handed to
// ParseSdf, because how many values an entry listed is exactly what the file
// says and nothing else.

// Parses, elaborates, lowers and runs `src`, then registers with the manager
// the two kinds of declaration §32.8 distinguishes -- the module paths and the
// primitives driving module outputs -- through the production builders.
bool BuildDesign(const std::string& src, SimFixture& f, SpecifyManager& mgr) {
  auto* cu = RunModuleSource(src, f);
  if (cu == nullptr) return false;
  const ModuleDecl& mod = *cu->modules.back();
  RegisterPrimitiveDrivers(mod, f, mgr);
  RegisterPathDelays(mod, f, mgr);
  return true;
}

// Parses `sdf` and annotates it onto an already-populated manager. `mtm` is the
// member a delay value written as a min:typ:max triple contributes.
void AnnotateFileOnto(const std::string& sdf, SpecifyManager& mgr,
                      SdfMtm mtm = SdfMtm::kTypical) {
  SdfFile file;
  EXPECT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, mtm);
}

// Wraps one DELAY-section body in the surrounding SDF a cell needs, for a
// section that states its values outright.
std::string DelaySdf(const std::string& entries) {
  return "(DELAYFILE (CELL (CELLTYPE \"t\") (INSTANCE u1) (DELAY (ABSOLUTE " +
         entries + ")))) ";
}

// The same wrapper for a section whose values change what the design already
// carries rather than replacing it.
std::string IncrementDelaySdf(const std::string& entries) {
  return "(DELAYFILE (CELL (CELLTYPE \"t\") (INSTANCE u1) (DELAY (INCREMENT " +
         entries + ")))) ";
}

// The same wrapper for the top-level cell, which is the one an interconnect
// entry belongs to: its port names cross instance boundaries of that cell.
std::string TopDelaySdf(const std::string& entries) {
  const std::string kHead =
      "(DELAYFILE (CELL (CELLTYPE \"top\") (INSTANCE top) (DELAY (ABSOLUTE ";
  return kHead + entries + ")))) ";
}

// The module path that carries twelve state transition delays. Its declaration
// lists six of them (§30.5.1), all distinct and none of them a value any test
// below annotates, so a transition slot the annotation failed to reach reads as
// a leftover rather than as a coincidence.
const char* const kPathDesign =
    "module t(input a, output y);\n"
    "  specify\n"
    "    (a => y) = (11, 12, 13, 14, 15, 16);\n"
    "  endspecify\n"
    "endmodule\n";

// The construct §32.8 contrasts the module path with: a gate primitive, which
// carries three state transition delays. The module declares no specify path,
// which is what makes a DEVICE entry land on the primitive driving the output
// rather than on a path (§32.4.1 Table 32-1). Its three declared delays are
// again distinct from everything annotated below, and small, so a value added
// to one of them is still telling them apart.
//
// The gate is one that can drive its output to the high-impedance state. §28.16
// allows the third delay -- the turn-off delay -- only on such a gate, so `buf`
// and the rest that cannot be turned off take two delays at most, and three
// written on one of them is not a declaration at all.
const char* const kGateDesign =
    "module t(input a, input en, output y);\n"
    "  bufif1 #(1, 2, 3) g1(y, a, en);\n"
    "endmodule\n";

// One instance driving another over a net of the top module, which is the
// design shape an interconnect delay is annotated across. Interconnects are the
// second construct §32.8 says carries twelve transition delays.
const char* const kInterconnectDesign =
    "module drv(q);\n"
    "  output q;\n"
    "  reg q;\n"
    "endmodule\n"
    "module ld(d);\n"
    "  input d;\n"
    "  wire d;\n"
    "endmodule\n"
    "module top;\n"
    "  wire n;\n"
    "  drv u1(.q(n));\n"
    "  ld u2(.d(n));\n"
    "endmodule\n";

// Builds the two-instance design and hands the manager its connectivity, which
// is what an interconnect entry's port names are looked up in -- there is no
// declaration behind such a delay to match against instead.
bool BuildInterconnectDesign(SdfDesign& d) {
  if (!d.Lower(kInterconnectDesign)) return false;
  d.mgr.BindDesignInterconnect(CollectInterconnectTopology(*d.cu, d.Top()));
  return true;
}

const PathDelay* PathAToY(const SpecifyManager& mgr) {
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.src_port == "a" && pd.dst_port == "y") return &pd;
  }
  return nullptr;
}

const PrimitiveDriver* DriverOfY(const SpecifyManager& mgr) {
  for (const auto& drv : mgr.GetPrimitiveDrivers()) {
    if (drv.output_port == "y") return &drv;
  }
  return nullptr;
}

// The interconnect delay annotated onto the load port of the pair design.
const InterconnectDelay* LoadOfU2D(const SpecifyManager& mgr) {
  for (const auto& ic : mgr.GetInterconnectDelays()) {
    if (ic.dst_port == "u2/d") return &ic;
  }
  return nullptr;
}

// The twelve transition slots §32.8 names, in the order Table 32-4 lists its
// rows: 0->1, 1->0, 0->z, z->1, 1->z, z->0, 0->x, x->1, 1->x, x->0, x->z, z->x.
constexpr int kTransitions = 12;

// ---------------------------------------------------------------------------
// Table 32-4: a specify path's twelve transition delays, filled in from the
// values one IOPATH entry listed. Each test below differs from the next only in
// how many values its entry writes, because that count is what chooses the
// column of the table the twelve slots come from.
// ---------------------------------------------------------------------------

TEST(SdfTwelveTransitionMapping, OneIopathValueReachesEveryTransition) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));
  ASSERT_NE(PathAToY(mgr), nullptr);

  AnnotateFileOnto(DelaySdf("(IOPATH a y (5))"), mgr);

  // The one value the file wrote reaches all twelve, so no slot is left holding
  // any of the six the declaration spread over them.
  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], 5u) << "transition slot " << i;
  }
}

TEST(SdfTwelveTransitionMapping, TwoIopathValuesKeepRiseAndFallFamiliesApart) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y (5) (9))"), mgr);

  // Every transition that starts a rise takes the first value and every one
  // that starts a fall the second; the last two rows of the table are the two
  // the second column derives, x->z from the larger and z->x from the smaller.
  const uint64_t kExpected[kTransitions] = {5, 9, 5, 5, 9, 9, 5, 5, 9, 9, 9, 5};
  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], kExpected[i]) << "transition slot " << i;
  }
}

TEST(SdfTwelveTransitionMapping, ThreeIopathValuesAddTheTurnOffFamily) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y (4) (6) (9))"), mgr);

  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 4u);   // 0->1 rise
  EXPECT_EQ(pd->delays[1], 6u);   // 1->0 fall
  EXPECT_EQ(pd->delays[2], 9u);   // 0->z turn-off
  EXPECT_EQ(pd->delays[3], 4u);   // z->1 rise
  EXPECT_EQ(pd->delays[4], 9u);   // 1->z turn-off
  EXPECT_EQ(pd->delays[5], 6u);   // z->0 fall
  EXPECT_EQ(pd->delays[6], 4u);   // 0->x smaller of rise and turn-off
  EXPECT_EQ(pd->delays[8], 6u);   // 1->x smaller of fall and turn-off
  EXPECT_EQ(pd->delays[9], 6u);   // x->0 fall
  EXPECT_EQ(pd->delays[10], 9u);  // x->z turn-off
  EXPECT_EQ(pd->delays[11], 4u);  // z->x smaller of rise and fall
  // The x->1 slot of this column is left unpinned here: the value the tree
  // computes for it disagrees with the row Table 32-4 gives, and another
  // subclause's test already fixes the tree's value, so which of the two
  // readings is right is not settled inside this file.
}

TEST(SdfTwelveTransitionMapping, SixIopathValuesDeriveTheXTransitions) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y (7) (3) (9) (2) (8) (4))"), mgr);

  // The six the entry wrote fill the six transitions that name no x state, and
  // the six that do reach x are each derived from a pair of them. The values
  // are deliberately out of order so a slot taking its neighbour's value cannot
  // read as the right answer.
  const uint64_t kExpected[kTransitions] = {7, 3, 9, 2, 8, 4, 7, 7, 3, 4, 9, 2};
  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], kExpected[i]) << "transition slot " << i;
  }
}

TEST(SdfTwelveTransitionMapping, TwelveIopathValuesAreTakenAsWritten) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y (21) (22) (23) (24) (25) (26)"
                            " (27) (28) (29) (30) (31) (32))"),
                   mgr);

  // A file that supplies all twelve leaves nothing to derive.
  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], static_cast<uint64_t>(21 + i))
        << "transition slot " << i;
  }
}

// ---------------------------------------------------------------------------
// The second way an entry writes a delay value. Each of the values the table
// spreads may be a min:typ:max triple rather than a bare number, and the member
// the run selects is the one that goes on to fill the transitions. The spread
// is the same either way, so each selection is checked over all twelve slots
// rather than only where the value first lands.
// ---------------------------------------------------------------------------

TEST(SdfTwelveTransitionMapping, MinTypMaxValuesSpreadTheirMinimumMember) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y (1:2:3) (4:5:6))"), mgr,
                   SdfMtm::kMinimum);

  const uint64_t kExpected[kTransitions] = {1, 4, 1, 1, 4, 4, 1, 1, 4, 4, 4, 1};
  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], kExpected[i]) << "transition slot " << i;
  }
}

TEST(SdfTwelveTransitionMapping, MinTypMaxValuesSpreadTheirTypicalMember) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y (1:2:3) (4:5:6))"), mgr,
                   SdfMtm::kTypical);

  const uint64_t kExpected[kTransitions] = {2, 5, 2, 2, 5, 5, 2, 2, 5, 5, 5, 2};
  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], kExpected[i]) << "transition slot " << i;
  }
}

TEST(SdfTwelveTransitionMapping, MinTypMaxValuesSpreadTheirMaximumMember) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y (1:2:3) (4:5:6))"), mgr,
                   SdfMtm::kMaximum);

  const uint64_t kExpected[kTransitions] = {3, 6, 3, 3, 6, 6, 3, 3, 6, 6, 6, 3};
  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], kExpected[i]) << "transition slot " << i;
  }
}

// ---------------------------------------------------------------------------
// The second way an IOPATH writes its value list. In the extended spelling
// each direction is a parenthesized group carrying a delay and, optionally,
// the pulse limits that go with it, so what counts towards the table's column
// is how many direction groups were written rather than how many bare values.
// ---------------------------------------------------------------------------

TEST(SdfTwelveTransitionMapping, OneExtendedDirectionReachesEveryTransition) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y ((6)))"), mgr);

  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], 6u) << "transition slot " << i;
  }
}

TEST(SdfTwelveTransitionMapping, TwoExtendedDirectionsKeepTheFamiliesApart) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  // Each direction also carries its two pulse limits, which is what makes this
  // spelling extended; they are no part of the value list the table spreads, so
  // the entry is still a two-value one.
  AnnotateFileOnto(DelaySdf("(IOPATH a y ((6) (2) (3)) ((8) (2) (3)))"), mgr);

  const uint64_t kExpected[kTransitions] = {6, 8, 6, 6, 8, 8, 6, 6, 8, 8, 8, 6};
  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], kExpected[i]) << "transition slot " << i;
  }
}

// ---------------------------------------------------------------------------
// The other construct §32.8 names as carrying twelve transition delays. An
// interconnect delay has no SystemVerilog declaration behind it, so an entry is
// matched against the design's own connectivity; the mapping from the values it
// listed onto the twelve slots is still the one table. Which keyword wrote the
// entry -- INTERCONNECT, PORT or NETDELAY -- changes only how its target is
// named, which is §32.4.4's rule and covered there; all three reach the same
// value list and the same mapping, so one of them drives it here.
// ---------------------------------------------------------------------------

TEST(SdfTwelveTransitionMapping, SixInterconnectValuesDeriveTheXTransitions) {
  SdfDesign d;
  ASSERT_TRUE(BuildInterconnectDesign(d));

  AnnotateFileOnto(
      TopDelaySdf("(INTERCONNECT u1/q u2/d (7) (3) (9) (2) (8) (4))"), d.mgr);

  const uint64_t kExpected[kTransitions] = {7, 3, 9, 2, 8, 4, 7, 7, 3, 4, 9, 2};
  const InterconnectDelay* got = LoadOfU2D(d.mgr);
  ASSERT_NE(got, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(got->delays[i], kExpected[i]) << "transition slot " << i;
  }
}

// ---------------------------------------------------------------------------
// The other constructs: a gate primitive carries three state transition delays,
// so an entry that lists more than three loses the extras, and the delay to the
// x state is worked out from the three that remain.
// ---------------------------------------------------------------------------

TEST(SdfThreeTransitionMapping, MoreThanThreeDeviceValuesLoseTheExtras) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kGateDesign, f, mgr));
  ASSERT_NE(DriverOfY(mgr), nullptr);

  AnnotateFileOnto(DelaySdf("(DEVICE (30) (10) (20) (40) (50) (60))"), mgr);

  const PrimitiveDriver* drv = DriverOfY(mgr);
  ASSERT_NE(drv, nullptr);
  // The first three values are the three the primitive keeps, and they spread
  // over the six transitions that name no x state the way a three-delay
  // declaration spreads: rise, fall, turn-off, then rise, turn-off, fall.
  EXPECT_EQ(drv->delays[0], 30u);  // 0->1 rise
  EXPECT_EQ(drv->delays[1], 10u);  // 1->0 fall
  EXPECT_EQ(drv->delays[2], 20u);  // 0->z turn-off
  EXPECT_EQ(drv->delays[3], 30u);  // z->1 rise
  EXPECT_EQ(drv->delays[4], 20u);  // 1->z turn-off
  EXPECT_EQ(drv->delays[5], 10u);  // z->0 fall
  // The fourth, fifth and sixth values are the extras. Nothing they could have
  // reached holds them: had the primitive been filled in the way a specify path
  // is, the z->1 slot above would carry the fourth value instead of the first.
  const uint64_t kDropped[3] = {40, 50, 60};
  for (uint64_t dropped : kDropped) {
    for (int i = 0; i < kTransitions; ++i) {
      EXPECT_NE(drv->delays[i], dropped) << "slot " << i << " has " << dropped;
    }
  }
}

TEST(SdfThreeTransitionMapping, DeviceDelayToTheXStateIsTheSmallestOfThree) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kGateDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(DEVICE (30) (10) (20) (40) (50) (60))"), mgr);

  const PrimitiveDriver* drv = DriverOfY(mgr);
  ASSERT_NE(drv, nullptr);
  // The middle value is the smallest of the three retained, so a slot reaching
  // x that took a pair of the three rather than all three would read 20 here
  // rather than 10.
  EXPECT_EQ(drv->delays[6], 10u);   // 0->x
  EXPECT_EQ(drv->delays[8], 10u);   // 1->x
  EXPECT_EQ(drv->delays[11], 10u);  // z->x
}

// ---------------------------------------------------------------------------
// The same two rules where the entry states changes to what the primitive
// already carries rather than stating its delays outright. The reduction runs
// first either way: what is added is the three values that survived it and the
// one delay to the x state they produced, never the extras.
// ---------------------------------------------------------------------------

TEST(SdfThreeTransitionMapping, IncrementDeviceAddsOnlyTheThreeItKept) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kGateDesign, f, mgr));
  const PrimitiveDriver* before = DriverOfY(mgr);
  ASSERT_NE(before, nullptr);
  ASSERT_EQ(before->delays[3], 1u);  // z->1, the gate's declared rise

  AnnotateFileOnto(IncrementDelaySdf("(DEVICE (30) (10) (20) (40) (50) (60))"),
                   mgr);

  const PrimitiveDriver* drv = DriverOfY(mgr);
  ASSERT_NE(drv, nullptr);
  EXPECT_EQ(drv->delays[0], 31u);  // 0->1, 30 onto the declared 1
  EXPECT_EQ(drv->delays[1], 12u);  // 1->0, 10 onto the declared 2
  EXPECT_EQ(drv->delays[2], 23u);  // 0->z, 20 onto the declared 3
  // The z->1 slot is where the extras would show: an entry whose fourth value
  // reached the primitive would leave 41 here rather than the rise again.
  EXPECT_EQ(drv->delays[3], 31u);
  EXPECT_EQ(drv->delays[4], 23u);  // 1->z turn-off
  EXPECT_EQ(drv->delays[5], 12u);  // z->0 fall
}

TEST(SdfThreeTransitionMapping, IncrementDeviceRaisesTheXDelayByTheSmallest) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kGateDesign, f, mgr));
  const PrimitiveDriver* before = DriverOfY(mgr);
  ASSERT_NE(before, nullptr);
  ASSERT_EQ(before->delays[6], 1u);  // 0->x as the declaration left it

  AnnotateFileOnto(IncrementDelaySdf("(DEVICE (30) (10) (20) (40) (50) (60))"),
                   mgr);

  const PrimitiveDriver* drv = DriverOfY(mgr);
  ASSERT_NE(drv, nullptr);
  // The smallest of the three kept values is 10, and it is that one amount the
  // single delay to the x state goes up by -- not the 22 a slot derived from a
  // pair of the incremented three would show.
  EXPECT_EQ(drv->delays[6], 11u);   // 0->x
  EXPECT_EQ(drv->delays[8], 11u);   // 1->x
  EXPECT_EQ(drv->delays[11], 11u);  // z->x
}

// The negative form for the reduction: the closest input it must leave alone is
// the same entry reaching a construct that does carry twelve transition delays.
// Nothing is dropped there, and the fourth, fifth and sixth values land in the
// transitions Table 32-4 gives them rather than going unused.
TEST(SdfThreeTransitionMapping, DeviceOnASpecifyPathKeepsAllTwelve) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildDesign(kPathDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(DEVICE (30) (10) (20) (40) (50) (60))"), mgr);

  const uint64_t kExpected[kTransitions] = {30, 10, 20, 40, 50, 60,
                                            20, 40, 10, 60, 50, 40};
  const PathDelay* pd = PathAToY(mgr);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < kTransitions; ++i) {
    EXPECT_EQ(pd->delays[i], kExpected[i]) << "transition slot " << i;
  }
}

}  // namespace
