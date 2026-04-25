#include <gtest/gtest.h>

#include <string>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// =============================================================================
// §32.4.2 — Mapping of SDF timing check constructs to SystemVerilog
// =============================================================================

// Helper to register a SystemVerilog timing check declaration with the
// identity fields the §32.4.2 matching rule consults. Limits start at
// zero so individual tests can pin specific pre-annotation values when
// the table's "x" cells require them to survive.
TimingCheckEntry MakeSv(TimingCheckKind kind, const char* ref_signal,
                        const char* data_signal,
                        SpecifyEdge ref_edge = SpecifyEdge::kNone,
                        SpecifyEdge data_edge = SpecifyEdge::kNone,
                        const char* condition = "") {
  TimingCheckEntry tc;
  tc.kind = kind;
  tc.ref_signal = ref_signal;
  tc.data_signal = data_signal;
  tc.ref_edge = ref_edge;
  tc.data_edge = data_edge;
  tc.condition = condition;
  return tc;
}

// Build a single-cell SdfFile carrying `tc` so a test can hand a pre-built
// SDF timing check to the annotator without going through the SDF lexer.
SdfFile WrapTimingCheck(SdfTimingCheck tc) {
  SdfFile file;
  SdfCell cell;
  cell.timing_checks.push_back(std::move(tc));
  file.cells.push_back(std::move(cell));
  return file;
}

// Table 32-2 row "(SETUP v1...) → $setup(v1), $setuphold(v1,x)" — one
// SDF SETUP fans out to two SystemVerilog targets. The `x` cell on the
// $setuphold mapping requires the SystemVerilog $setuphold's hold limit
// (limit2) to be left at its prebackannotation value rather than
// collapsed to zero.
TEST(SdfTimingCheckMapping, SetupExpandsToSetupAndSetupholdSetupSlot) {
  SpecifyManager mgr;
  TimingCheckEntry sv_setup = MakeSv(TimingCheckKind::kSetup, "clk", "d");
  sv_setup.limit = 1;
  mgr.AddTimingCheck(sv_setup);
  TimingCheckEntry sv_sh = MakeSv(TimingCheckKind::kSetuphold, "clk", "d");
  sv_sh.limit = 2;
  sv_sh.limit2 = 7;
  mgr.AddTimingCheck(sv_sh);

  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kSetup;
  tc.ref_port = "clk";
  tc.data_port = "d";
  tc.limit.typ_val = 50;
  AnnotateSdfToManager(WrapTimingCheck(tc), mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.TimingCheckCount(), 2u);
  for (const auto& t : mgr.GetTimingChecks()) {
    if (t.kind == TimingCheckKind::kSetup) {
      EXPECT_EQ(t.limit, 50u);
    } else if (t.kind == TimingCheckKind::kSetuphold) {
      EXPECT_EQ(t.limit, 50u);
      EXPECT_EQ(t.limit2, 7u);
    } else {
      ADD_FAILURE() << "unexpected kind";
    }
  }
}

// Table 32-2 row "(HOLD v1...) → $hold(v1), $setuphold(x,v1)" — the
// symmetric counterpart: the `x` is on $setuphold's setup slot (limit),
// so the SystemVerilog $setuphold's setup limit survives while v1 lands
// in limit2.
TEST(SdfTimingCheckMapping, HoldExpandsToHoldAndSetupholdHoldSlot) {
  SpecifyManager mgr;
  TimingCheckEntry sv_hold = MakeSv(TimingCheckKind::kHold, "clk", "d");
  sv_hold.limit = 1;
  mgr.AddTimingCheck(sv_hold);
  TimingCheckEntry sv_sh = MakeSv(TimingCheckKind::kSetuphold, "clk", "d");
  sv_sh.limit = 7;
  sv_sh.limit2 = 2;
  mgr.AddTimingCheck(sv_sh);

  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kHold;
  tc.ref_port = "clk";
  tc.data_port = "d";
  tc.limit.typ_val = 99;
  AnnotateSdfToManager(WrapTimingCheck(tc), mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.TimingCheckCount(), 2u);
  for (const auto& t : mgr.GetTimingChecks()) {
    if (t.kind == TimingCheckKind::kHold) {
      EXPECT_EQ(t.limit, 99u);
    } else if (t.kind == TimingCheckKind::kSetuphold) {
      EXPECT_EQ(t.limit, 7u);
      EXPECT_EQ(t.limit2, 99u);
    } else {
      ADD_FAILURE() << "unexpected kind";
    }
  }
}

// Table 32-2 row "(SETUPHOLD v1 v2...) → $setup(v1), $hold(v2),
// $setuphold(v1,v2)" — one SDF construct fans out to three SystemVerilog
// targets and populates both halves of $setuphold from a single pass.
TEST(SdfTimingCheckMapping, SetupholdExpandsToSetupHoldAndSetuphold) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSv(TimingCheckKind::kSetup, "clk", "d"));
  mgr.AddTimingCheck(MakeSv(TimingCheckKind::kHold, "clk", "d"));
  mgr.AddTimingCheck(MakeSv(TimingCheckKind::kSetuphold, "clk", "d"));

  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kSetuphold;
  tc.ref_port = "clk";
  tc.data_port = "d";
  tc.limit.typ_val = 11;
  tc.limit2.typ_val = 22;
  AnnotateSdfToManager(WrapTimingCheck(tc), mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.TimingCheckCount(), 3u);
  for (const auto& t : mgr.GetTimingChecks()) {
    if (t.kind == TimingCheckKind::kSetup) {
      EXPECT_EQ(t.limit, 11u);
    } else if (t.kind == TimingCheckKind::kHold) {
      EXPECT_EQ(t.limit, 22u);
    } else if (t.kind == TimingCheckKind::kSetuphold) {
      EXPECT_EQ(t.limit, 11u);
      EXPECT_EQ(t.limit2, 22u);
    }
  }
}

// Table 32-2 row "(RECOVERY v1...) → $recovery(v1), $recrem(v1,x)" — the
// $recrem half-mapping mirrors SETUP→$setuphold: removal limit (limit2)
// stays at its prebackannotation value while v1 lands on the recovery
// slot (limit).
TEST(SdfTimingCheckMapping, RecoveryExpandsToRecoveryAndRecremRecoverySlot) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSv(TimingCheckKind::kRecovery, "clk", "rst"));
  TimingCheckEntry sv_rr = MakeSv(TimingCheckKind::kRecrem, "clk", "rst");
  sv_rr.limit = 3;
  sv_rr.limit2 = 9;
  mgr.AddTimingCheck(sv_rr);

  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kRecovery;
  tc.ref_port = "clk";
  tc.data_port = "rst";
  tc.limit.typ_val = 44;
  AnnotateSdfToManager(WrapTimingCheck(tc), mgr, SdfMtm::kTypical);

  for (const auto& t : mgr.GetTimingChecks()) {
    if (t.kind == TimingCheckKind::kRecovery) {
      EXPECT_EQ(t.limit, 44u);
    } else if (t.kind == TimingCheckKind::kRecrem) {
      EXPECT_EQ(t.limit, 44u);
      EXPECT_EQ(t.limit2, 9u);
    }
  }
}

// Table 32-2 row "(REMOVAL v1...) → $removal(v1), $recrem(x,v1)" —
// symmetric to RECOVERY: recovery slot (limit) of $recrem is preserved;
// v1 lands in limit2.
TEST(SdfTimingCheckMapping, RemovalExpandsToRemovalAndRecremRemovalSlot) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSv(TimingCheckKind::kRemoval, "clk", "rst"));
  TimingCheckEntry sv_rr = MakeSv(TimingCheckKind::kRecrem, "clk", "rst");
  sv_rr.limit = 9;
  sv_rr.limit2 = 3;
  mgr.AddTimingCheck(sv_rr);

  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kRemoval;
  tc.ref_port = "clk";
  tc.data_port = "rst";
  tc.limit.typ_val = 77;
  AnnotateSdfToManager(WrapTimingCheck(tc), mgr, SdfMtm::kTypical);

  for (const auto& t : mgr.GetTimingChecks()) {
    if (t.kind == TimingCheckKind::kRemoval) {
      EXPECT_EQ(t.limit, 77u);
    } else if (t.kind == TimingCheckKind::kRecrem) {
      EXPECT_EQ(t.limit, 9u);
      EXPECT_EQ(t.limit2, 77u);
    }
  }
}

// Table 32-2 row "(RECREM v1 v2...) → $recovery(v1), $removal(v2),
// $recrem(v1,v2)" — three-target fan-out that populates both halves of
// $recrem in a single annotation pass.
TEST(SdfTimingCheckMapping, RecremExpandsToRecoveryRemovalAndRecrem) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSv(TimingCheckKind::kRecovery, "clk", "rst"));
  mgr.AddTimingCheck(MakeSv(TimingCheckKind::kRemoval, "clk", "rst"));
  mgr.AddTimingCheck(MakeSv(TimingCheckKind::kRecrem, "clk", "rst"));

  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kRecrem;
  tc.ref_port = "clk";
  tc.data_port = "rst";
  tc.limit.typ_val = 5;
  tc.limit2.typ_val = 8;
  AnnotateSdfToManager(WrapTimingCheck(tc), mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.TimingCheckCount(), 3u);
  for (const auto& t : mgr.GetTimingChecks()) {
    if (t.kind == TimingCheckKind::kRecovery) {
      EXPECT_EQ(t.limit, 5u);
    } else if (t.kind == TimingCheckKind::kRemoval) {
      EXPECT_EQ(t.limit, 8u);
    } else if (t.kind == TimingCheckKind::kRecrem) {
      EXPECT_EQ(t.limit, 5u);
      EXPECT_EQ(t.limit2, 8u);
    }
  }
}

// Table 32-2 row "(SKEW v1...) → $skew(v1), $timeskew(v1)" — a single
// SDF SKEW updates both kinds with the same v1, even though the two
// timing checks are independent SystemVerilog invocations.
TEST(SdfTimingCheckMapping, SkewExpandsToSkewAndTimeskew) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSv(TimingCheckKind::kSkew, "clk1", "clk2"));
  mgr.AddTimingCheck(MakeSv(TimingCheckKind::kTimeskew, "clk1", "clk2"));

  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kSkew;
  tc.ref_port = "clk1";
  tc.data_port = "clk2";
  tc.limit.typ_val = 12;
  AnnotateSdfToManager(WrapTimingCheck(tc), mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.TimingCheckCount(), 2u);
  bool saw_skew = false;
  bool saw_timeskew = false;
  for (const auto& t : mgr.GetTimingChecks()) {
    EXPECT_EQ(t.limit, 12u);
    if (t.kind == TimingCheckKind::kSkew) saw_skew = true;
    if (t.kind == TimingCheckKind::kTimeskew) saw_timeskew = true;
  }
  EXPECT_TRUE(saw_skew);
  EXPECT_TRUE(saw_timeskew);
}

// Table 32-2 row "(BIDIRECTSKEW v1 v2...) → $fullskew(v1,v2)" — the only
// row whose SDF construct has no same-named SystemVerilog timing check;
// $fullskew is the sole target and receives both v1 and v2.
TEST(SdfTimingCheckMapping, BidirectskewExpandsToFullskewWithBothLimits) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSv(TimingCheckKind::kFullskew, "clk1", "clk2"));

  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kBidirectskew;
  tc.ref_port = "clk1";
  tc.data_port = "clk2";
  tc.limit.typ_val = 4;
  tc.limit2.typ_val = 6;
  AnnotateSdfToManager(WrapTimingCheck(tc), mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.TimingCheckCount(), 1u);
  EXPECT_EQ(mgr.GetTimingChecks()[0].kind, TimingCheckKind::kFullskew);
  EXPECT_EQ(mgr.GetTimingChecks()[0].limit, 4u);
  EXPECT_EQ(mgr.GetTimingChecks()[0].limit2, 6u);
}

// Table 32-2 row "(WIDTH v1...) → $width(v1,x)" — only the limit is
// annotated; the `x` second argument is the §31.4.4 glitch threshold,
// which must keep its prebackannotation value rather than collapse to
// zero from the SDF pass.
TEST(SdfTimingCheckMapping, WidthExpandsToWidthAndPreservesThreshold) {
  SpecifyManager mgr;
  TimingCheckEntry sv = MakeSv(TimingCheckKind::kWidth, "clk", "");
  sv.limit = 1;
  sv.threshold = 13;
  mgr.AddTimingCheck(sv);

  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kWidth;
  tc.ref_port = "clk";
  tc.limit.typ_val = 50;
  AnnotateSdfToManager(WrapTimingCheck(tc), mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.TimingCheckCount(), 1u);
  EXPECT_EQ(mgr.GetTimingChecks()[0].limit, 50u);
  EXPECT_EQ(mgr.GetTimingChecks()[0].threshold, 13u);
}

// Table 32-2 row "(PERIOD v1...) → $period(v1)" — single-target row;
// the $period limit is updated.
TEST(SdfTimingCheckMapping, PeriodExpandsToPeriod) {
  SpecifyManager mgr;
  TimingCheckEntry sv = MakeSv(TimingCheckKind::kPeriod, "clk", "");
  sv.limit = 1;
  mgr.AddTimingCheck(sv);

  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kPeriod;
  tc.ref_port = "clk";
  tc.limit.typ_val = 100;
  AnnotateSdfToManager(WrapTimingCheck(tc), mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.TimingCheckCount(), 1u);
  EXPECT_EQ(mgr.GetTimingChecks()[0].kind, TimingCheckKind::kPeriod);
  EXPECT_EQ(mgr.GetTimingChecks()[0].limit, 100u);
}

// Table 32-2 row "(NOCHANGE v1 v2...) → $nochange(v1,v2)" — §31.4.6
// names $nochange's two arguments start_edge_offset and end_edge_offset,
// which TimingCheckEntry stores on dedicated signed fields. The SDF
// v1/v2 must land there rather than on the limit fields.
TEST(SdfTimingCheckMapping, NochangeExpandsToNochangeWithEdgeOffsets) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSv(TimingCheckKind::kNochange, "clk", "d"));

  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kNochange;
  tc.ref_port = "clk";
  tc.data_port = "d";
  tc.limit.typ_val = 3;
  tc.limit2.typ_val = 4;
  AnnotateSdfToManager(WrapTimingCheck(tc), mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.TimingCheckCount(), 1u);
  EXPECT_EQ(mgr.GetTimingChecks()[0].kind, TimingCheckKind::kNochange);
  EXPECT_EQ(mgr.GetTimingChecks()[0].start_edge_offset, 3);
  EXPECT_EQ(mgr.GetTimingChecks()[0].end_edge_offset, 4);
}

// =============================================================================
// §32.4.2 paragraph 2 — Condition/edge matching
// =============================================================================

// Paragraph 2 sentence 2: "When conditions and/or edges are associated
// with the signals in an SDF timing check, then they shall match those
// in any corresponding SystemVerilog timing check before annotation
// shall happen." Three pre-loaded SystemVerilog $setup checks differ
// only on the reference edge; an SDF SETUP carrying `posedge` must
// update only the `posedge` sibling.
TEST(SdfTimingCheckMapping, SdfWithRefEdgeAnnotatesOnlyMatchingSvEdge) {
  SpecifyManager mgr;
  TimingCheckEntry pos = MakeSv(TimingCheckKind::kSetup, "clk", "d",
                                SpecifyEdge::kPosedge);
  pos.limit = 1;
  mgr.AddTimingCheck(pos);
  TimingCheckEntry neg = MakeSv(TimingCheckKind::kSetup, "clk", "d",
                                SpecifyEdge::kNegedge);
  neg.limit = 2;
  mgr.AddTimingCheck(neg);
  TimingCheckEntry any = MakeSv(TimingCheckKind::kSetup, "clk", "d",
                                SpecifyEdge::kEdge);
  any.limit = 3;
  mgr.AddTimingCheck(any);

  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kSetup;
  tc.ref_port = "clk";
  tc.data_port = "d";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit.typ_val = 99;
  AnnotateSdfToManager(WrapTimingCheck(tc), mgr, SdfMtm::kTypical);

  for (const auto& t : mgr.GetTimingChecks()) {
    if (t.kind != TimingCheckKind::kSetup) continue;
    if (t.ref_edge == SpecifyEdge::kPosedge) {
      EXPECT_EQ(t.limit, 99u);
    } else if (t.ref_edge == SpecifyEdge::kNegedge) {
      EXPECT_EQ(t.limit, 2u);
    } else if (t.ref_edge == SpecifyEdge::kEdge) {
      EXPECT_EQ(t.limit, 3u);
    }
  }
}

// Paragraph 2 sentence 2 — condition variant: a non-empty SDF condition
// must match the SystemVerilog `&&&` condition exactly. The sibling
// SystemVerilog check whose condition differs keeps its
// prebackannotation value.
TEST(SdfTimingCheckMapping, SdfWithConditionAnnotatesOnlyMatchingSvCondition) {
  SpecifyManager mgr;
  TimingCheckEntry m = MakeSv(TimingCheckKind::kSetup, "clk", "d",
                              SpecifyEdge::kNone, SpecifyEdge::kNone, "mode");
  m.limit = 1;
  mgr.AddTimingCheck(m);
  TimingCheckEntry nm = MakeSv(TimingCheckKind::kSetup, "clk", "d",
                               SpecifyEdge::kNone, SpecifyEdge::kNone,
                               "!mode");
  nm.limit = 2;
  mgr.AddTimingCheck(nm);

  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kSetup;
  tc.ref_port = "clk";
  tc.data_port = "d";
  tc.condition = "mode";
  tc.limit.typ_val = 99;
  AnnotateSdfToManager(WrapTimingCheck(tc), mgr, SdfMtm::kTypical);

  for (const auto& t : mgr.GetTimingChecks()) {
    if (t.kind != TimingCheckKind::kSetup) continue;
    if (t.condition == "mode") {
      EXPECT_EQ(t.limit, 99u);
    } else if (t.condition == "!mode") {
      EXPECT_EQ(t.limit, 2u);
    }
  }
}

// Paragraph 2 example (page 926): an SDF SETUPHOLD with no conditions
// or edges shall annotate to all corresponding SystemVerilog timing
// checks. Three $setuphold siblings differ on edge and condition; a
// bare SDF SETUPHOLD updates every one's setup and hold limits.
TEST(SdfTimingCheckMapping,
     BareSdfSetupholdMatchesAllSvSetupholdsRegardlessOfEdgeOrCondition) {
  SpecifyManager mgr;
  TimingCheckEntry a = MakeSv(TimingCheckKind::kSetuphold, "clk", "data",
                              SpecifyEdge::kPosedge, SpecifyEdge::kNone,
                              "mode");
  mgr.AddTimingCheck(a);
  TimingCheckEntry b = MakeSv(TimingCheckKind::kSetuphold, "clk", "data",
                              SpecifyEdge::kNegedge, SpecifyEdge::kNone,
                              "!mode");
  mgr.AddTimingCheck(b);
  TimingCheckEntry c = MakeSv(TimingCheckKind::kSetuphold, "clk", "data",
                              SpecifyEdge::kEdge);
  mgr.AddTimingCheck(c);

  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kSetuphold;
  tc.ref_port = "clk";
  tc.data_port = "data";
  tc.limit.typ_val = 3;
  tc.limit2.typ_val = 4;
  AnnotateSdfToManager(WrapTimingCheck(tc), mgr, SdfMtm::kTypical);

  uint32_t setuphold_seen = 0;
  for (const auto& t : mgr.GetTimingChecks()) {
    if (t.kind != TimingCheckKind::kSetuphold) continue;
    EXPECT_EQ(t.limit, 3u);
    EXPECT_EQ(t.limit2, 4u);
    ++setuphold_seen;
  }
  EXPECT_EQ(setuphold_seen, 3u);
}

// Paragraph 2 example (page 927): an SDF SETUPHOLD with an edge on the
// reference signal but no condition shall annotate to a SystemVerilog
// $setuphold whose reference event has the same edge — even when the
// SystemVerilog check carries an additional `&&&` condition. This pins
// the asymmetric reading of the "shall match those" rule: the matcher
// only checks the SystemVerilog property when the SDF specifies a
// corresponding restriction, so an SDF that left condition unspecified
// must not exclude SystemVerilog checks that happen to have one.
TEST(SdfTimingCheckMapping, SdfWithRefEdgeMatchesSvDespiteSvCondition) {
  SpecifyManager mgr;
  TimingCheckEntry sv = MakeSv(TimingCheckKind::kSetuphold, "clk", "data",
                               SpecifyEdge::kPosedge, SpecifyEdge::kNone,
                               "mode");
  sv.limit = 1;
  sv.limit2 = 2;
  mgr.AddTimingCheck(sv);

  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kSetuphold;
  tc.ref_port = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_port = "data";
  tc.limit.typ_val = 3;
  tc.limit2.typ_val = 4;
  AnnotateSdfToManager(WrapTimingCheck(tc), mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.TimingCheckCount(), 1u);
  EXPECT_EQ(mgr.GetTimingChecks()[0].limit, 3u);
  EXPECT_EQ(mgr.GetTimingChecks()[0].limit2, 4u);
  // The SystemVerilog declaration's own condition text survives the
  // pass — the annotator updates payload, not identity.
  EXPECT_EQ(mgr.GetTimingChecks()[0].condition, "mode");
}

// Paragraph 2 example (page 928): an SDF check carrying both an edge
// and a condition requires both restrictions to hold simultaneously
// before the SystemVerilog check is annotated. Three pre-loaded
// $setuphold siblings each agree with only one of the SDF's
// restrictions, so none of them are eligible and every one keeps its
// prebackannotation values. This pins the conjunctive reading of the
// "and/or are associated" wording — the matcher must AND the
// restrictions, not OR them.
TEST(SdfTimingCheckMapping,
     SdfWithBothRefEdgeAndConditionRequiresBothToMatch) {
  SpecifyManager mgr;
  TimingCheckEntry mode_pos = MakeSv(TimingCheckKind::kSetuphold, "clk",
                                     "data", SpecifyEdge::kPosedge,
                                     SpecifyEdge::kNone, "mode");
  mode_pos.limit = 11;
  mode_pos.limit2 = 12;
  mgr.AddTimingCheck(mode_pos);
  TimingCheckEntry notmode_neg = MakeSv(TimingCheckKind::kSetuphold, "clk",
                                        "data", SpecifyEdge::kNegedge,
                                        SpecifyEdge::kNone, "!mode");
  notmode_neg.limit = 21;
  notmode_neg.limit2 = 22;
  mgr.AddTimingCheck(notmode_neg);
  TimingCheckEntry edge_only = MakeSv(TimingCheckKind::kSetuphold, "clk",
                                      "data", SpecifyEdge::kEdge);
  edge_only.limit = 31;
  edge_only.limit2 = 32;
  mgr.AddTimingCheck(edge_only);

  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kSetuphold;
  tc.ref_port = "clk";
  tc.data_port = "data";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.condition = "!mode";
  tc.limit.typ_val = 99;
  tc.limit2.typ_val = 88;
  AnnotateSdfToManager(WrapTimingCheck(tc), mgr, SdfMtm::kTypical);

  // Each pre-existing sibling fails one half of the SDF's restriction
  // (mode_pos has wrong condition, notmode_neg has wrong edge,
  // edge_only has wrong edge and missing condition) so none of them
  // shall be touched. The annotator may still append a fresh entry to
  // record the unmatched SDF data; the rule under test is only that
  // the three pre-existing siblings retain their values.
  for (const auto& t : mgr.GetTimingChecks()) {
    if (t.ref_edge == SpecifyEdge::kPosedge && t.condition == "mode") {
      EXPECT_EQ(t.limit, 11u);
      EXPECT_EQ(t.limit2, 12u);
    } else if (t.ref_edge == SpecifyEdge::kNegedge &&
               t.condition == "!mode") {
      EXPECT_EQ(t.limit, 21u);
      EXPECT_EQ(t.limit2, 22u);
    } else if (t.ref_edge == SpecifyEdge::kEdge && t.condition.empty()) {
      EXPECT_EQ(t.limit, 31u);
      EXPECT_EQ(t.limit2, 32u);
    }
  }
}

// =============================================================================
// §32.4.2 parser support — BIDIRECTSKEW and the new TIMINGCHECK shapes
// =============================================================================

// §32.4.2 Table 32-2 names BIDIRECTSKEW as one of the SDF timing check
// constructs the annotator must recognise; the parser must tokenise the
// keyword and route it to SdfCheckType::kBidirectskew so the table's
// $fullskew row applies.
TEST(SdfTimingCheckMapping, BidirectskewKeywordParsesIntoEnum) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "io")
        (INSTANCE u1)
        (TIMINGCHECK
          (BIDIRECTSKEW c1 c2 (4) (6))
        )
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  ASSERT_EQ(file.cells[0].timing_checks.size(), 1u);
  EXPECT_EQ(file.cells[0].timing_checks[0].check_type,
            SdfCheckType::kBidirectskew);
  EXPECT_EQ(file.cells[0].timing_checks[0].limit.typ_val, 4u);
  EXPECT_EQ(file.cells[0].timing_checks[0].limit2.typ_val, 6u);
}

// §32.4.2 Table 32-2 single-signal rows (WIDTH, PERIOD): the parser
// must not consume a phantom second port — these constructs reference
// one signal only.
TEST(SdfTimingCheckMapping, WidthParsesSingleSignalForm) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "ff")
        (INSTANCE u1)
        (TIMINGCHECK
          (WIDTH (posedge clk) (5))
        )
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  ASSERT_EQ(file.cells[0].timing_checks.size(), 1u);
  EXPECT_EQ(file.cells[0].timing_checks[0].check_type, SdfCheckType::kWidth);
  EXPECT_EQ(file.cells[0].timing_checks[0].ref_port, "clk");
  EXPECT_EQ(file.cells[0].timing_checks[0].ref_edge, SpecifyEdge::kPosedge);
  EXPECT_TRUE(file.cells[0].timing_checks[0].data_port.empty());
  EXPECT_EQ(file.cells[0].timing_checks[0].limit.typ_val, 5u);
}

// §32.4.2 paragraph 3 example (page 928): the parser must lift the
// condition out of a (COND <expr> (edge port)) wrapper on a timing
// check signal and stamp it onto the SdfTimingCheck so the annotator's
// per-property matcher can compare it against SystemVerilog's `&&&`
// condition. Without this plumbing, the paragraph-3 condition rule is
// unreachable from real SDF text.
TEST(SdfTimingCheckMapping, CondWrappedSignalCarriesConditionToTimingCheck) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "ff")
        (INSTANCE u1)
        (TIMINGCHECK
          (SETUPHOLD data (COND !mode (posedge clk)) (3) (4))
        )
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  ASSERT_EQ(file.cells[0].timing_checks.size(), 1u);
  const auto& tc = file.cells[0].timing_checks[0];
  EXPECT_EQ(tc.check_type, SdfCheckType::kSetuphold);
  EXPECT_EQ(tc.data_port, "data");
  EXPECT_EQ(tc.ref_port, "clk");
  EXPECT_EQ(tc.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.condition, "!mode");
  EXPECT_EQ(tc.limit.typ_val, 3u);
  EXPECT_EQ(tc.limit2.typ_val, 4u);
}

// §32.4.2 paragraph 3 example (page 928), end-to-end: feeding the
// SDF text through ParseSdf and AnnotateSdfToManager must reach the
// matcher with both the edge and the condition restrictions applied,
// leaving every SystemVerilog sibling that disagrees on either
// property at its prebackannotation values.
TEST(SdfTimingCheckMapping,
     ParsedCondWrappedSetupholdAnnotatesNoneOfMismatchedSiblings) {
  SpecifyManager mgr;
  TimingCheckEntry mode_pos = MakeSv(TimingCheckKind::kSetuphold, "clk",
                                     "data", SpecifyEdge::kPosedge,
                                     SpecifyEdge::kNone, "mode");
  mode_pos.limit = 11;
  mode_pos.limit2 = 12;
  mgr.AddTimingCheck(mode_pos);
  TimingCheckEntry notmode_neg = MakeSv(TimingCheckKind::kSetuphold, "clk",
                                        "data", SpecifyEdge::kNegedge,
                                        SpecifyEdge::kNone, "!mode");
  notmode_neg.limit = 21;
  notmode_neg.limit2 = 22;
  mgr.AddTimingCheck(notmode_neg);
  TimingCheckEntry edge_only = MakeSv(TimingCheckKind::kSetuphold, "clk",
                                      "data", SpecifyEdge::kEdge);
  edge_only.limit = 31;
  edge_only.limit2 = 32;
  mgr.AddTimingCheck(edge_only);

  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "ff")
        (INSTANCE u1)
        (TIMINGCHECK
          (SETUPHOLD data (COND !mode (posedge clk)) (3) (4))
        )
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  for (const auto& t : mgr.GetTimingChecks()) {
    if (t.ref_edge == SpecifyEdge::kPosedge && t.condition == "mode") {
      EXPECT_EQ(t.limit, 11u);
      EXPECT_EQ(t.limit2, 12u);
    } else if (t.ref_edge == SpecifyEdge::kNegedge &&
               t.condition == "!mode") {
      EXPECT_EQ(t.limit, 21u);
      EXPECT_EQ(t.limit2, 22u);
    } else if (t.ref_edge == SpecifyEdge::kEdge && t.condition.empty()) {
      EXPECT_EQ(t.limit, 31u);
      EXPECT_EQ(t.limit2, 32u);
    }
  }
}

// §32.4.2 Table 32-2 two-value rows (SETUPHOLD, RECREM, BIDIRECTSKEW,
// NOCHANGE): the parser must capture both v1 and v2 so the annotator
// can populate every SystemVerilog target the row dictates.
TEST(SdfTimingCheckMapping, SetupholdParsesBothLimitValues) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "ff")
        (INSTANCE u1)
        (TIMINGCHECK
          (SETUPHOLD d (posedge clk) (3) (4))
        )
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  ASSERT_EQ(file.cells[0].timing_checks.size(), 1u);
  EXPECT_EQ(file.cells[0].timing_checks[0].check_type,
            SdfCheckType::kSetuphold);
  EXPECT_EQ(file.cells[0].timing_checks[0].limit.typ_val, 3u);
  EXPECT_EQ(file.cells[0].timing_checks[0].limit2.typ_val, 4u);
}

}  // namespace
