#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_specify_manager.h"
#include "simulator/evaluation.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// §32.4.1 says which SystemVerilog *declaration* each SDF delay construct lands
// on, so which declarations exist -- and how each one was written -- is the
// whole subject. Every test below therefore builds its SystemVerilog side from
// real source: BuildSpecifyFromSource parses, elaborates and runs a module and
// then fills a SpecifyManager from that module using only production builders.
// Module path assignments come in through §30.4.2/§30.4.4/§30.4.4.4 syntax and
// BuildPathDelayFromDecl, PATHPULSE$ pulse limits through §30.7.1's resolver,
// timing checks through §31.2/§31.7 declarations, and the primitives that drive
// module outputs through gate instantiations. Nothing here is hand-assembled.
bool BuildSpecifyFromSource(const std::string& src, SimFixture& f,
                            SpecifyManager& mgr) {
  auto* cu = RunModuleSource(src, f);
  if (cu == nullptr) return false;
  const ModuleDecl& mod = *cu->modules.back();
  RegisterPrimitiveDrivers(mod, f, mgr);
  RegisterPathDelays(mod, f, mgr, /*default_pulse_limits=*/true);
  RegisterTimingChecks(mod, f, mgr);
  RegisterPathPulseSpecparams(mod, f, mgr);
  return true;
}

// The design most tests annotate onto. Between a and y it declares the three
// forms a module path can take that differ only by condition -- two
// state-dependent paths (§30.4.4/§30.4.4.1) and the ifnone path that covers the
// rest (§30.4.4.4) -- so a construct that is supposed to reach one of them can
// be checked against the two it must leave alone. The b to z path (§30.4.2) is
// the unconditional endpoint pair no a-to-y construct may touch. Every declared
// value is distinct, so untouched never reads as overwritten. The two $setup
// checks differ only by condition and the $hold only by type, which is what
// makes the timing check matching rule observable.
const char* const kDesign =
    "module t(input a, input b, input mode, input clk, input d,\n"
    "         output y, output z);\n"
    "  reg ntf;\n"
    "  specify\n"
    "    if (mode)  (a => y) = 21;\n"
    "    if (!mode) (a => y) = 22;\n"
    "    ifnone     (a => y) = 23;\n"
    "    (b => z) = 24;\n"
    "    $setup(posedge clk &&& mode, d, 41, ntf);\n"
    "    $setup(posedge clk &&& !mode, d, 42, ntf);\n"
    "    $hold(posedge clk, d, 51, ntf);\n"
    "  endspecify\n"
    "endmodule\n";

// Locates one declared module path by everything §32.4.1 matches on: its two
// endpoint names plus the condition it was declared under.
const PathDelay* PathWith(const SpecifyManager& mgr, std::string_view src,
                          std::string_view dst, std::string_view condition,
                          bool is_ifnone) {
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.src_port == src && pd.dst_port == dst && pd.condition == condition &&
        pd.is_ifnone == is_ifnone) {
      return &pd;
    }
  }
  return nullptr;
}

const PathDelay* IfMode(const SpecifyManager& mgr) {
  return PathWith(mgr, "a", "y", "mode", false);
}
const PathDelay* IfNotMode(const SpecifyManager& mgr) {
  return PathWith(mgr, "a", "y", "!mode", false);
}
const PathDelay* Ifnone(const SpecifyManager& mgr) {
  return PathWith(mgr, "a", "y", "", true);
}
const PathDelay* BToZ(const SpecifyManager& mgr) {
  return PathWith(mgr, "b", "z", "", false);
}

// Reads back one declared timing check by type and by the condition it was
// declared under, which together are what an SDF timing check has to match.
const TimingCheckEntry* CheckWith(const SpecifyManager& mgr,
                                  TimingCheckKind kind,
                                  std::string_view condition) {
  for (const auto& tc : mgr.GetTimingChecks()) {
    if (tc.kind == kind && tc.condition == condition) return &tc;
  }
  return nullptr;
}

// Reads back the delays recorded for the primitive driving `output`.
const PrimitiveDriver* DriverOf(const SpecifyManager& mgr,
                                std::string_view output) {
  for (const auto& drv : mgr.GetPrimitiveDrivers()) {
    if (drv.output_port == output) return &drv;
  }
  return nullptr;
}

// Parses |sdf| and annotates it onto an already-populated manager.
SdfAnnotationResult AnnotateFileOnto(const std::string& sdf,
                                     SpecifyManager& mgr) {
  SdfFile file;
  EXPECT_TRUE(ParseSdf(sdf, file));
  return AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
}

// Wraps one DELAY-section body in the surrounding SDF a cell needs.
std::string DelaySdf(const std::string& entries) {
  return "(DELAYFILE (CELL (CELLTYPE \"t\") (INSTANCE u1) (DELAY (ABSOLUTE " +
         entries + ")))) ";
}

// Wraps one TIMINGCHECK-section body the same way.
std::string TimingCheckSdf(const std::string& entries) {
  return "(DELAYFILE (CELL (CELLTYPE \"t\") (INSTANCE u1) (TIMINGCHECK " +
         entries + "))) ";
}

// ---------------------------------------------------------------------------
// A nonconditional IOPATH annotates to all specify paths between those ports.
// ---------------------------------------------------------------------------

TEST(SdfDelayMapping, NonconditionalIopathReachesEveryPathBetweenThosePorts) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y (13) (17))"), mgr);

  // Every a-to-y path is reached, whatever condition it was declared under,
  // and each keeps the condition it was declared with.
  for (const PathDelay* pd : {IfMode(mgr), IfNotMode(mgr), Ifnone(mgr)}) {
    ASSERT_NE(pd, nullptr);
    EXPECT_EQ(pd->delays[0], 13u);
    EXPECT_EQ(pd->delays[1], 17u);
  }
  // The names have to match too: the other endpoint pair is left alone.
  ASSERT_NE(BToZ(mgr), nullptr);
  EXPECT_EQ(BToZ(mgr)->delays[0], 24u);
}

TEST(SdfDelayMapping, NonconditionalIopathLeavesTheOtherEndpointsAlone) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH b z (18))"), mgr);

  ASSERT_NE(BToZ(mgr), nullptr);
  EXPECT_EQ(BToZ(mgr)->delays[0], 18u);
  ASSERT_NE(IfMode(mgr), nullptr);
  EXPECT_EQ(IfMode(mgr)->delays[0], 21u);
  ASSERT_NE(IfNotMode(mgr), nullptr);
  EXPECT_EQ(IfNotMode(mgr)->delays[0], 22u);
  ASSERT_NE(Ifnone(mgr), nullptr);
  EXPECT_EQ(Ifnone(mgr)->delays[0], 23u);
}

// The rule is about the endpoint names, not about how the delay it replaces was
// written. §30.5 admits a module path delay written as a literal, as a
// specparam, as an expression over specparams, or as a min:typ:max triple of
// them; a path is reached the same way whichever of those it was declared with.
TEST(SdfDelayMapping, IopathReachesPathsHoweverTheirDelayWasWritten) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(
      "module c(input a, input b, input e, input g,\n"
      "         output w, output x, output y, output z);\n"
      "  specify\n"
      "    specparam S = 31;\n"
      "    specparam T = 1;\n"
      "    (a => w) = 30;\n"
      "    (b => x) = S;\n"
      "    (e => y) = S + T;\n"
      "    (g => z) = 33:34:35;\n"
      "  endspecify\n"
      "endmodule\n",
      f, mgr));

  ASSERT_NE(PathWith(mgr, "b", "x", "", false), nullptr);
  EXPECT_EQ(PathWith(mgr, "b", "x", "", false)->delays[0], 31u);
  ASSERT_NE(PathWith(mgr, "e", "y", "", false), nullptr);
  EXPECT_EQ(PathWith(mgr, "e", "y", "", false)->delays[0], 32u);

  AnnotateFileOnto(DelaySdf("(IOPATH a w (11)) (IOPATH b x (12))"
                            "(IOPATH e y (13)) (IOPATH g z (14))"),
                   mgr);

  EXPECT_EQ(PathWith(mgr, "a", "w", "", false)->delays[0], 11u);
  EXPECT_EQ(PathWith(mgr, "b", "x", "", false)->delays[0], 12u);
  EXPECT_EQ(PathWith(mgr, "e", "y", "", false)->delays[0], 13u);
  EXPECT_EQ(PathWith(mgr, "g", "z", "", false)->delays[0], 14u);
}

// ---------------------------------------------------------------------------
// A conditional IOPATH annotates only to paths between those same two ports
// carrying the same condition.
// ---------------------------------------------------------------------------

TEST(SdfDelayMapping, ConditionalIopathReachesOnlyTheSameConditionPath) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(COND mode (IOPATH a y (13) (17)))"), mgr);

  ASSERT_NE(IfMode(mgr), nullptr);
  EXPECT_EQ(IfMode(mgr)->delays[0], 13u);
  EXPECT_EQ(IfMode(mgr)->delays[1], 17u);
  // Same endpoints, different condition: not reached.
  ASSERT_NE(IfNotMode(mgr), nullptr);
  EXPECT_EQ(IfNotMode(mgr)->delays[0], 22u);
  // The ifnone path answers to CONDELSE, not to a condition of its own.
  ASSERT_NE(Ifnone(mgr), nullptr);
  EXPECT_EQ(Ifnone(mgr)->delays[0], 23u);
  // Different endpoints: not reached either.
  ASSERT_NE(BToZ(mgr), nullptr);
  EXPECT_EQ(BToZ(mgr)->delays[0], 24u);
}

// The negative form of the same rule: a condition no declared path carries
// reaches none of them. "Only" also rules out the entry landing somewhere new,
// so the module must come out of backannotation with exactly the four paths it
// declared -- a fifth one carrying the file's condition would be a specify path
// the design never wrote.
TEST(SdfDelayMapping, ConditionalIopathWithAnUnmatchedConditionReachesNothing) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));
  ASSERT_EQ(mgr.GetPathDelays().size(), 4u);

  AnnotateFileOnto(DelaySdf("(COND other (IOPATH a y (13) (17)))"), mgr);

  EXPECT_EQ(mgr.GetPathDelays().size(), 4u);
  EXPECT_EQ(PathWith(mgr, "a", "y", "other", false), nullptr);
  EXPECT_EQ(IfMode(mgr)->delays[0], 21u);
  EXPECT_EQ(IfNotMode(mgr)->delays[0], 22u);
  EXPECT_EQ(Ifnone(mgr)->delays[0], 23u);
  EXPECT_EQ(BToZ(mgr)->delays[0], 24u);
}

// The same restriction for CONDELSE: with no ifnone path declared between those
// ports, the entry has nothing to annotate and creates nothing.
TEST(SdfDelayMapping, CondelseIopathWithNoIfnonePathDeclaredReachesNothing) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(
      BuildSpecifyFromSource("module n(input b, output z);\n"
                             "  specify\n"
                             "    (b => z) = 24;\n"
                             "  endspecify\n"
                             "endmodule\n",
                             f, mgr));
  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);

  AnnotateFileOnto(DelaySdf("(CONDELSE (IOPATH b z (13) (17)))"), mgr);

  EXPECT_EQ(mgr.GetPathDelays().size(), 1u);
  EXPECT_EQ(PathWith(mgr, "b", "z", "", true), nullptr);
  ASSERT_NE(PathWith(mgr, "b", "z", "", false), nullptr);
  EXPECT_EQ(PathWith(mgr, "b", "z", "", false)->delays[0], 24u);
}

// Same-condition is not enough on its own: the endpoint names still have to
// match, so a conditional entry naming other ports leaves the same-condition
// path alone.
TEST(SdfDelayMapping, ConditionalIopathStillHasToMatchTheEndpointNames) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  ASSERT_EQ(mgr.GetPathDelays().size(), 4u);

  AnnotateFileOnto(DelaySdf("(COND mode (IOPATH b z (13) (17)))"), mgr);

  EXPECT_EQ(mgr.GetPathDelays().size(), 4u);
  EXPECT_EQ(IfMode(mgr)->delays[0], 21u);
  EXPECT_EQ(BToZ(mgr)->delays[0], 24u);
}

// A second condition form. The conditions matched so far are a bare signal and
// its negation; §30.4.4.1 also admits a comparison, which reaches the annotator
// as a different shape of expression entirely. Matching still has to pick out
// the one path whose condition is the same one.
TEST(SdfDelayMapping, ConditionalIopathMatchesAComparisonCondition) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(
      BuildSpecifyFromSource("module k(input a, input mode, output y);\n"
                             "  specify\n"
                             "    if (mode == 1) (a => y) = 21;\n"
                             "    if (mode == 0) (a => y) = 22;\n"
                             "  endspecify\n"
                             "endmodule\n",
                             f, mgr));

  AnnotateFileOnto(DelaySdf("(COND mode == 1 (IOPATH a y (13) (17)))"), mgr);

  const PathDelay* matched = PathWith(mgr, "a", "y", "mode == 1", false);
  ASSERT_NE(matched, nullptr);
  EXPECT_EQ(matched->delays[0], 13u);
  EXPECT_EQ(matched->delays[1], 17u);
  const PathDelay* other = PathWith(mgr, "a", "y", "mode == 0", false);
  ASSERT_NE(other, nullptr);
  EXPECT_EQ(other->delays[0], 22u);
}

// ---------------------------------------------------------------------------
// CONDELSE annotates to ifnone.
// ---------------------------------------------------------------------------

TEST(SdfDelayMapping, CondelseIopathReachesOnlyTheIfnonePath) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(CONDELSE (IOPATH a y (13) (17)))"), mgr);

  ASSERT_NE(Ifnone(mgr), nullptr);
  EXPECT_EQ(Ifnone(mgr)->delays[0], 13u);
  EXPECT_EQ(Ifnone(mgr)->delays[1], 17u);
  EXPECT_EQ(IfMode(mgr)->delays[0], 21u);
  EXPECT_EQ(IfNotMode(mgr)->delays[0], 22u);
  EXPECT_EQ(BToZ(mgr)->delays[0], 24u);
}

// ---------------------------------------------------------------------------
// A RETAIN qualifier may be ignored: it changes neither the delays annotated
// nor which paths they reach, in any of the three forms that admit it.
// ---------------------------------------------------------------------------

TEST(SdfDelayMapping, IopathRetainChangesNeitherDelaysNorPathsReached) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y (RETAIN (3) (4)) (13) (17))"), mgr);

  for (const PathDelay* pd : {IfMode(mgr), IfNotMode(mgr), Ifnone(mgr)}) {
    ASSERT_NE(pd, nullptr);
    EXPECT_EQ(pd->delays[0], 13u);
    EXPECT_EQ(pd->delays[1], 17u);
  }
  EXPECT_EQ(BToZ(mgr)->delays[0], 24u);
}

TEST(SdfDelayMapping, CondIopathRetainChangesNeitherDelaysNorPathsReached) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  AnnotateFileOnto(
      DelaySdf("(COND mode (IOPATH a y (RETAIN (1) (2)) (13) (17)))"), mgr);

  ASSERT_NE(IfMode(mgr), nullptr);
  EXPECT_EQ(IfMode(mgr)->delays[0], 13u);
  EXPECT_EQ(IfMode(mgr)->delays[1], 17u);
  EXPECT_EQ(IfNotMode(mgr)->delays[0], 22u);
  EXPECT_EQ(Ifnone(mgr)->delays[0], 23u);
}

TEST(SdfDelayMapping, CondelseIopathRetainChangesNeitherDelaysNorPathsReached) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(CONDELSE (IOPATH a y (RETAIN (1)) (13) (17)))"),
                   mgr);

  ASSERT_NE(Ifnone(mgr), nullptr);
  EXPECT_EQ(Ifnone(mgr)->delays[0], 13u);
  EXPECT_EQ(Ifnone(mgr)->delays[1], 17u);
  EXPECT_EQ(IfMode(mgr)->delays[0], 21u);
  EXPECT_EQ(IfNotMode(mgr)->delays[0], 22u);
}

// ---------------------------------------------------------------------------
// PATHPULSE and PATHPULSEPERCENT annotate specify path pulse limits, on
// conditional and nonconditional paths alike.
// ---------------------------------------------------------------------------

TEST(SdfDelayMapping, PathpulseSetsTheLimitsOfEveryPathBetweenThosePorts) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(PATHPULSE a y (5) (15))"), mgr);

  for (const PathDelay* pd : {IfMode(mgr), IfNotMode(mgr), Ifnone(mgr)}) {
    ASSERT_NE(pd, nullptr);
    EXPECT_EQ(pd->reject_limit[0], 5u);
    EXPECT_EQ(pd->error_limit[0], 15u);
  }
  // Only the limits are provided, so the propagation delays are left as
  // declared, and the path this entry does not name keeps its own limits.
  EXPECT_EQ(IfMode(mgr)->delays[0], 21u);
  ASSERT_NE(BToZ(mgr), nullptr);
  EXPECT_EQ(BToZ(mgr)->reject_limit[0], 24u);
  EXPECT_EQ(BToZ(mgr)->error_limit[0], 24u);
}

// The limits an SDF PATHPULSE replaces can just as well have come from a
// PATHPULSE$ specparam (§30.7.1) as from the §30.7 default.
TEST(SdfDelayMapping, PathpulseReplacesLimitsSetByAPathpulseSpecparam) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(
      BuildSpecifyFromSource("module p(input a, input b, output y, output z);\n"
                             "  specify\n"
                             "    specparam PATHPULSE$a$y = (2, 9);\n"
                             "    (a => y) = 21;\n"
                             "    (b => z) = 24;\n"
                             "  endspecify\n"
                             "endmodule\n",
                             f, mgr));

  const PathDelay* declared = PathWith(mgr, "a", "y", "", false);
  ASSERT_NE(declared, nullptr);
  EXPECT_EQ(declared->reject_limit[0], 2u);
  EXPECT_EQ(declared->error_limit[0], 9u);

  AnnotateFileOnto(DelaySdf("(PATHPULSE a y (5) (15))"), mgr);

  EXPECT_EQ(PathWith(mgr, "a", "y", "", false)->reject_limit[0], 5u);
  EXPECT_EQ(PathWith(mgr, "a", "y", "", false)->error_limit[0], 15u);
  EXPECT_EQ(PathWith(mgr, "b", "z", "", false)->reject_limit[0], 24u);
}

// A PATHPULSE may carry a single limit rather than a pair. It reaches the same
// paths, with the one value standing in for both limits.
TEST(SdfDelayMapping, PathpulseWithOneValueSetsBothLimitsOfEveryPath) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(PATHPULSE a y (5))"), mgr);

  for (const PathDelay* pd : {IfMode(mgr), IfNotMode(mgr), Ifnone(mgr)}) {
    ASSERT_NE(pd, nullptr);
    EXPECT_EQ(pd->reject_limit[0], 5u);
    EXPECT_EQ(pd->error_limit[0], 5u);
  }
  ASSERT_NE(BToZ(mgr), nullptr);
  EXPECT_EQ(BToZ(mgr)->reject_limit[0], 24u);
}

// The negative form: a PATHPULSE has to match endpoint names like any other
// delay construct, so one naming ports the module declares no path between
// leaves every declared path's limits as they were.
TEST(SdfDelayMapping, PathpulseNamingUndeclaredPortsReachesNothing) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(PATHPULSE q r (5) (15))"), mgr);

  EXPECT_EQ(IfMode(mgr)->reject_limit[0], 21u);
  EXPECT_EQ(IfMode(mgr)->error_limit[0], 21u);
  EXPECT_EQ(IfNotMode(mgr)->reject_limit[0], 22u);
  EXPECT_EQ(Ifnone(mgr)->reject_limit[0], 23u);
  EXPECT_EQ(BToZ(mgr)->reject_limit[0], 24u);
}

TEST(SdfDelayMapping, PathpulsepercentScalesTheLimitsFromThePathDelay) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(PATHPULSEPERCENT b z (25) (75))"), mgr);

  ASSERT_NE(BToZ(mgr), nullptr);
  EXPECT_EQ(BToZ(mgr)->delays[0], 24u);
  EXPECT_EQ(BToZ(mgr)->reject_limit[0], 6u);  // 25% of 24
  EXPECT_EQ(BToZ(mgr)->error_limit[0], 18u);  // 75% of 24
  // The paths this entry does not name keep the limits they were declared with.
  EXPECT_EQ(IfMode(mgr)->reject_limit[0], 21u);
}

// PATHPULSEPERCENT reaches conditional paths on the same terms as it reaches
// nonconditional ones, scaling each one from the delay that path was declared
// with rather than from a single shared value.
TEST(SdfDelayMapping, PathpulsepercentScalesTheLimitsOfConditionalPathsToo) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(PATHPULSEPERCENT a y (25) (75))"), mgr);

  ASSERT_NE(IfMode(mgr), nullptr);
  EXPECT_EQ(IfMode(mgr)->reject_limit[0], 5u);  // 25% of 21
  EXPECT_EQ(IfMode(mgr)->error_limit[0], 15u);  // 75% of 21
  ASSERT_NE(IfNotMode(mgr), nullptr);
  EXPECT_EQ(IfNotMode(mgr)->reject_limit[0], 5u);  // 25% of 22
  EXPECT_EQ(IfNotMode(mgr)->error_limit[0], 16u);  // 75% of 22
  ASSERT_NE(Ifnone(mgr), nullptr);
  EXPECT_EQ(Ifnone(mgr)->reject_limit[0], 5u);  // 25% of 23
  EXPECT_EQ(Ifnone(mgr)->error_limit[0], 17u);  // 75% of 23
  ASSERT_NE(BToZ(mgr), nullptr);
  EXPECT_EQ(BToZ(mgr)->reject_limit[0], 24u);
}

// The single-value form of the percentage entry: the one percentage sets both
// limits, each still scaled from the delay of the path it reaches.
TEST(SdfDelayMapping, PathpulsepercentWithOnePercentSetsBothLimits) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(PATHPULSEPERCENT b z (50))"), mgr);

  ASSERT_NE(BToZ(mgr), nullptr);
  EXPECT_EQ(BToZ(mgr)->delays[0], 24u);
  EXPECT_EQ(BToZ(mgr)->reject_limit[0], 12u);  // 50% of 24
  EXPECT_EQ(BToZ(mgr)->error_limit[0], 12u);
  EXPECT_EQ(IfMode(mgr)->reject_limit[0], 21u);
}

// ---------------------------------------------------------------------------
// An IOPATH annotates specify path pulse limits as well as delays.
// ---------------------------------------------------------------------------

TEST(SdfDelayMapping, IopathCarriesItsOwnPulseLimitsOntoThePath) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH b z ((30) (4) (9)) ((40) (4) (9)))"), mgr);

  ASSERT_NE(BToZ(mgr), nullptr);
  EXPECT_EQ(BToZ(mgr)->delays[0], 30u);
  EXPECT_EQ(BToZ(mgr)->delays[1], 40u);
  EXPECT_EQ(BToZ(mgr)->reject_limit[0], 4u);
  EXPECT_EQ(BToZ(mgr)->error_limit[0], 9u);
  EXPECT_EQ(IfMode(mgr)->delays[0], 21u);
}

// With no limits supplied by the file, the limits an IOPATH leaves on the path
// are the ones the global pulse-limit percentages (§30.7.2) select.
TEST(SdfDelayMapping, IopathPulseLimitsFollowTheGlobalPercentages) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));
  mgr.SetGlobalPulseLimitPercents(50, 80);

  AnnotateFileOnto(DelaySdf("(IOPATH b z (20) (20))"), mgr);

  ASSERT_NE(BToZ(mgr), nullptr);
  EXPECT_EQ(BToZ(mgr)->delays[0], 20u);
  EXPECT_EQ(BToZ(mgr)->reject_limit[0], 10u);
  EXPECT_EQ(BToZ(mgr)->error_limit[0], 16u);
}

// The pulse limits an IOPATH carries reach conditional paths too, not just the
// nonconditional ones the two tests above use.
TEST(SdfDelayMapping, NonconditionalIopathPulseLimitsReachConditionalPathsToo) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  AnnotateFileOnto(DelaySdf("(IOPATH a y ((30) (4) (9)) ((40) (4) (9)))"), mgr);

  for (const PathDelay* pd : {IfMode(mgr), IfNotMode(mgr), Ifnone(mgr)}) {
    ASSERT_NE(pd, nullptr);
    EXPECT_EQ(pd->delays[0], 30u);
    EXPECT_EQ(pd->delays[1], 40u);
    EXPECT_EQ(pd->reject_limit[0], 4u);
    EXPECT_EQ(pd->error_limit[0], 9u);
  }
  ASSERT_NE(BToZ(mgr), nullptr);
  EXPECT_EQ(BToZ(mgr)->reject_limit[0], 24u);
}

// A conditional IOPATH carries pulse limits the same way a nonconditional one
// does, and narrows them to the one path whose condition matches.
TEST(SdfDelayMapping, ConditionalIopathCarriesPulseLimitsOntoOnlyThatPath) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  AnnotateFileOnto(
      DelaySdf("(COND mode (IOPATH a y ((30) (4) (9)) ((40) (4) (9))))"), mgr);

  ASSERT_NE(IfMode(mgr), nullptr);
  EXPECT_EQ(IfMode(mgr)->delays[0], 30u);
  EXPECT_EQ(IfMode(mgr)->reject_limit[0], 4u);
  EXPECT_EQ(IfMode(mgr)->error_limit[0], 9u);
  // The same-endpoint path with the other condition keeps both its delay and
  // the limits it was declared with.
  ASSERT_NE(IfNotMode(mgr), nullptr);
  EXPECT_EQ(IfNotMode(mgr)->delays[0], 22u);
  EXPECT_EQ(IfNotMode(mgr)->reject_limit[0], 22u);
  EXPECT_EQ(IfNotMode(mgr)->error_limit[0], 22u);
}

// ---------------------------------------------------------------------------
// DEVICE: all specify paths to module outputs, or -- when there are none -- the
// primitives driving those outputs.
// ---------------------------------------------------------------------------

TEST(SdfDelayMapping, DeviceWithNoOperandReachesEverySpecifyPath) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  auto result = AnnotateFileOnto(DelaySdf("(DEVICE (7) (9))"), mgr);
  EXPECT_TRUE(result.warnings.empty());

  // Every path in the module ends at a module output, so every one is reached,
  // and each keeps the condition it was declared under.
  for (const PathDelay* pd :
       {IfMode(mgr), IfNotMode(mgr), Ifnone(mgr), BToZ(mgr)}) {
    ASSERT_NE(pd, nullptr);
    EXPECT_EQ(pd->delays[0], 7u);
    EXPECT_EQ(pd->delays[1], 9u);
  }
}

// The module declares no specify path at all, so the delay belongs to the gate
// primitives (§28) driving its outputs instead.
TEST(SdfDelayMapping, DeviceWithNoSpecifyPathsReachesTheDrivingPrimitives) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(
      BuildSpecifyFromSource("module g(input a, input b, output y, output z);\n"
                             "  buf #3 (y, a);\n"
                             "  buf #5 (z, b);\n"
                             "endmodule\n",
                             f, mgr));

  ASSERT_NE(DriverOf(mgr, "y"), nullptr);
  EXPECT_EQ(DriverOf(mgr, "y")->delays[0], 3u);
  ASSERT_NE(DriverOf(mgr, "z"), nullptr);
  EXPECT_EQ(DriverOf(mgr, "z")->delays[0], 5u);

  auto result = AnnotateFileOnto(DelaySdf("(DEVICE (7) (9))"), mgr);
  EXPECT_TRUE(result.warnings.empty());

  for (std::string_view output : {"y", "z"}) {
    ASSERT_NE(DriverOf(mgr, output), nullptr);
    EXPECT_EQ(DriverOf(mgr, output)->delays[0], 7u);
    EXPECT_EQ(DriverOf(mgr, output)->delays[1], 9u);
  }
}

// A second primitive form. The gate above is a buffer, whose output is the
// terminal the input does not occupy; a logic gate instead drives its leading
// terminal, so which signal counts as the driven output is worked out
// differently. The delay has to reach it just the same.
TEST(SdfDelayMapping, DeviceReachesALogicGateDrivingTheOutput) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(
      BuildSpecifyFromSource("module ag(input a, input b, output y);\n"
                             "  and #4 (y, a, b);\n"
                             "endmodule\n",
                             f, mgr));

  ASSERT_NE(DriverOf(mgr, "y"), nullptr);
  EXPECT_EQ(DriverOf(mgr, "y")->delays[0], 4u);

  auto result = AnnotateFileOnto(DelaySdf("(DEVICE (7) (9))"), mgr);
  EXPECT_TRUE(result.warnings.empty());

  EXPECT_EQ(DriverOf(mgr, "y")->delays[0], 7u);
  EXPECT_EQ(DriverOf(mgr, "y")->delays[1], 9u);
  // The gate's inputs are not outputs and pick up nothing.
  EXPECT_EQ(DriverOf(mgr, "a"), nullptr);
  EXPECT_EQ(DriverOf(mgr, "b"), nullptr);
}

// A third primitive form: one buffer driving two outputs at once. Both of them
// are module outputs the entry reaches.
TEST(SdfDelayMapping, DeviceReachesEveryOutputOfAMultiOutputPrimitive) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(
      BuildSpecifyFromSource("module bg(input a, output y, output z);\n"
                             "  buf #2 (y, z, a);\n"
                             "endmodule\n",
                             f, mgr));

  ASSERT_NE(DriverOf(mgr, "y"), nullptr);
  ASSERT_NE(DriverOf(mgr, "z"), nullptr);
  EXPECT_EQ(DriverOf(mgr, "z")->delays[0], 2u);

  AnnotateFileOnto(DelaySdf("(DEVICE (7) (9))"), mgr);

  for (std::string_view output : {"y", "z"}) {
    EXPECT_EQ(DriverOf(mgr, output)->delays[0], 7u);
    EXPECT_EQ(DriverOf(mgr, output)->delays[1], 9u);
  }
}

// The negative form for the whole row: with neither a specify path nor a
// driving primitive to land on, the entry reaches nothing and is reported
// rather than dropped (§32.3).
TEST(SdfDelayMapping, DeviceReachesNothingWithNoPathsAndNoPrimitives) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(
      BuildSpecifyFromSource("module e(input a, output y);\n"
                             "endmodule\n",
                             f, mgr));

  auto result = AnnotateFileOnto(DelaySdf("(DEVICE (7) (9))"), mgr);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("DEVICE"), std::string::npos);
  EXPECT_TRUE(mgr.GetPathDelays().empty());
  EXPECT_TRUE(mgr.GetPrimitiveDrivers().empty());
}

// The primitives are the fallback, not a second destination: a module that does
// declare a specify path has that path annotated and the gate driving its other
// output left as it was declared.
TEST(SdfDelayMapping, DeviceLeavesPrimitivesAloneWhenSpecifyPathsExist) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(
      BuildSpecifyFromSource("module m(input a, input b, output y, output z);\n"
                             "  buf #5 (z, b);\n"
                             "  specify\n"
                             "    (a => y) = 21;\n"
                             "  endspecify\n"
                             "endmodule\n",
                             f, mgr));

  auto result = AnnotateFileOnto(DelaySdf("(DEVICE (7) (9))"), mgr);
  EXPECT_TRUE(result.warnings.empty());

  ASSERT_NE(PathWith(mgr, "a", "y", "", false), nullptr);
  EXPECT_EQ(PathWith(mgr, "a", "y", "", false)->delays[0], 7u);
  ASSERT_NE(DriverOf(mgr, "z"), nullptr);
  EXPECT_EQ(DriverOf(mgr, "z")->delays[0], 5u);
}

// An operand naming one module output narrows the entry to the paths ending
// there.
TEST(SdfDelayMapping, DeviceOperandNamingAnOutputReachesOnlyThatOutputsPaths) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  auto result = AnnotateFileOnto(DelaySdf("(DEVICE y (7) (9))"), mgr);
  EXPECT_TRUE(result.warnings.empty());

  for (const PathDelay* pd : {IfMode(mgr), IfNotMode(mgr), Ifnone(mgr)}) {
    ASSERT_NE(pd, nullptr);
    EXPECT_EQ(pd->delays[0], 7u);
    EXPECT_EQ(pd->delays[1], 9u);
  }
  ASSERT_NE(BToZ(mgr), nullptr);
  EXPECT_EQ(BToZ(mgr)->delays[0], 24u);
}

// The same operand form, on an output the module declares no specify path for:
// the primitive driving that one output takes the delay, and the output that
// does have a path keeps it.
TEST(SdfDelayMapping, DeviceOperandNamingAPathlessOutputReachesItsPrimitive) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(
      BuildSpecifyFromSource("module m(input a, input b, output y, output z);\n"
                             "  buf #5 (z, b);\n"
                             "  specify\n"
                             "    (a => y) = 21;\n"
                             "  endspecify\n"
                             "endmodule\n",
                             f, mgr));

  auto result = AnnotateFileOnto(DelaySdf("(DEVICE z (7) (9))"), mgr);
  EXPECT_TRUE(result.warnings.empty());

  ASSERT_NE(DriverOf(mgr, "z"), nullptr);
  EXPECT_EQ(DriverOf(mgr, "z")->delays[0], 7u);
  EXPECT_EQ(DriverOf(mgr, "z")->delays[1], 9u);
  ASSERT_NE(PathWith(mgr, "a", "y", "", false), nullptr);
  EXPECT_EQ(PathWith(mgr, "a", "y", "", false)->delays[0], 21u);
}

// An operand narrows the primitive fallback the same way it narrows the paths:
// with two gates driving two outputs and no specify path anywhere, only the
// gate driving the named output is reached.
TEST(SdfDelayMapping, DeviceOperandNarrowsAmongSeveralDrivingPrimitives) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(
      "module tg(input a, input b, output y, output z);\n"
      "  buf #3 (y, a);\n"
      "  buf #5 (z, b);\n"
      "endmodule\n",
      f, mgr));

  auto result = AnnotateFileOnto(DelaySdf("(DEVICE z (7) (9))"), mgr);
  EXPECT_TRUE(result.warnings.empty());

  ASSERT_NE(DriverOf(mgr, "z"), nullptr);
  EXPECT_EQ(DriverOf(mgr, "z")->delays[0], 7u);
  EXPECT_EQ(DriverOf(mgr, "z")->delays[1], 9u);
  ASSERT_NE(DriverOf(mgr, "y"), nullptr);
  EXPECT_EQ(DriverOf(mgr, "y")->delays[0], 3u);
}

// The negative form: an operand naming no output this module declares reaches
// nothing, so nothing is modified and the data is reported (§32.3).
TEST(SdfDelayMapping, DeviceOperandNamingNoDeclaredOutputReachesNothing) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  auto result = AnnotateFileOnto(DelaySdf("(DEVICE sub (7) (9))"), mgr);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("DEVICE"), std::string::npos);
  EXPECT_EQ(IfMode(mgr)->delays[0], 21u);
  EXPECT_EQ(IfNotMode(mgr)->delays[0], 22u);
  EXPECT_EQ(Ifnone(mgr)->delays[0], 23u);
  EXPECT_EQ(BToZ(mgr)->delays[0], 24u);
}

// ---------------------------------------------------------------------------
// A TIMINGCHECK construct annotates to timing checks of the same type whose
// names and conditions match.
// ---------------------------------------------------------------------------

TEST(SdfTimingCheckMapping, ReachesOnlyChecksOfItsOwnType) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  // The declared $setup and $hold name the very same two signals, so type is
  // the only thing that keeps an SDF SETUP off the $hold.
  AnnotateFileOnto(TimingCheckSdf("(SETUP d (posedge clk) (7))"), mgr);

  const TimingCheckEntry* hold = CheckWith(mgr, TimingCheckKind::kHold, "");
  ASSERT_NE(hold, nullptr);
  EXPECT_EQ(hold->limit, 51u);
  const TimingCheckEntry* setup =
      CheckWith(mgr, TimingCheckKind::kSetup, "mode");
  ASSERT_NE(setup, nullptr);
  EXPECT_EQ(setup->limit, 7u);
}

TEST(SdfTimingCheckMapping, ReachesOnlyTheCheckWithTheSameCondition) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  AnnotateFileOnto(TimingCheckSdf("(SETUP d (COND mode (posedge clk)) (7))"),
                   mgr);

  const TimingCheckEntry* matched =
      CheckWith(mgr, TimingCheckKind::kSetup, "mode");
  ASSERT_NE(matched, nullptr);
  EXPECT_EQ(matched->limit, 7u);
  // Same type, same signals, different condition: not reached.
  const TimingCheckEntry* other =
      CheckWith(mgr, TimingCheckKind::kSetup, "!mode");
  ASSERT_NE(other, nullptr);
  EXPECT_EQ(other->limit, 42u);
  const TimingCheckEntry* hold = CheckWith(mgr, TimingCheckKind::kHold, "");
  ASSERT_NE(hold, nullptr);
  EXPECT_EQ(hold->limit, 51u);
}

// The other side of the same-type rule: a check type the module declares no
// counterpart for reaches nothing, even though its signals are named by checks
// that are declared. The constraint is reported rather than dropped (§32.3).
TEST(SdfTimingCheckMapping, ATypeTheModuleNeverDeclaresReachesNothing) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  auto result =
      AnnotateFileOnto(TimingCheckSdf("(WIDTH (posedge clk) (7))"), mgr);

  EXPECT_FALSE(result.warnings.empty());
  EXPECT_EQ(CheckWith(mgr, TimingCheckKind::kSetup, "mode")->limit, 41u);
  EXPECT_EQ(CheckWith(mgr, TimingCheckKind::kSetup, "!mode")->limit, 42u);
  EXPECT_EQ(CheckWith(mgr, TimingCheckKind::kHold, "")->limit, 51u);
  EXPECT_EQ(CheckWith(mgr, TimingCheckKind::kWidth, ""), nullptr);
}

// The negative form: the signal names have to match as well, so a check naming
// a signal the module never declared a check on reaches nothing at all.
TEST(SdfTimingCheckMapping, UnmatchedSignalNamesReachNothing) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));

  auto result =
      AnnotateFileOnto(TimingCheckSdf("(SETUP q (posedge clk) (7))"), mgr);

  EXPECT_FALSE(result.warnings.empty());
  EXPECT_EQ(CheckWith(mgr, TimingCheckKind::kSetup, "mode")->limit, 41u);
  EXPECT_EQ(CheckWith(mgr, TimingCheckKind::kSetup, "!mode")->limit, 42u);
  EXPECT_EQ(CheckWith(mgr, TimingCheckKind::kHold, "")->limit, 51u);
}

}  // namespace
