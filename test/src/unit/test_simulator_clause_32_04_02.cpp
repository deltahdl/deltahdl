#include <gtest/gtest.h>

#include <string>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

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

SdfFile WrapTimingCheck(SdfTimingCheck tc) {
  SdfFile file;
  SdfCell cell;
  cell.timing_checks.push_back(std::move(tc));
  file.cells.push_back(std::move(cell));
  return file;
}

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

TEST(SdfTimingCheckMapping, SdfWithRefEdgeAnnotatesOnlyMatchingSvEdge) {
  SpecifyManager mgr;
  TimingCheckEntry pos =
      MakeSv(TimingCheckKind::kSetup, "clk", "d", SpecifyEdge::kPosedge);
  pos.limit = 1;
  mgr.AddTimingCheck(pos);
  TimingCheckEntry neg =
      MakeSv(TimingCheckKind::kSetup, "clk", "d", SpecifyEdge::kNegedge);
  neg.limit = 2;
  mgr.AddTimingCheck(neg);
  TimingCheckEntry any =
      MakeSv(TimingCheckKind::kSetup, "clk", "d", SpecifyEdge::kEdge);
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

// An edge may sit on the data signal as well as the reference signal; when the
// SDF check carries a data-signal edge it must match the SystemVerilog check's
// data edge before annotation. Only the matching-edge sibling is updated.
TEST(SdfTimingCheckMapping, SdfWithDataEdgeAnnotatesOnlyMatchingSvDataEdge) {
  SpecifyManager mgr;
  TimingCheckEntry pos = MakeSv(TimingCheckKind::kSetup, "clk", "d",
                                SpecifyEdge::kNone, SpecifyEdge::kPosedge);
  pos.limit = 1;
  mgr.AddTimingCheck(pos);
  TimingCheckEntry neg = MakeSv(TimingCheckKind::kSetup, "clk", "d",
                                SpecifyEdge::kNone, SpecifyEdge::kNegedge);
  neg.limit = 2;
  mgr.AddTimingCheck(neg);

  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kSetup;
  tc.ref_port = "clk";
  tc.data_port = "d";
  tc.data_edge = SpecifyEdge::kPosedge;
  tc.limit.typ_val = 99;
  AnnotateSdfToManager(WrapTimingCheck(tc), mgr, SdfMtm::kTypical);

  for (const auto& t : mgr.GetTimingChecks()) {
    if (t.kind != TimingCheckKind::kSetup) continue;
    if (t.data_edge == SpecifyEdge::kPosedge) {
      EXPECT_EQ(t.limit, 99u);
    } else if (t.data_edge == SpecifyEdge::kNegedge) {
      EXPECT_EQ(t.limit, 2u);
    }
  }
}

TEST(SdfTimingCheckMapping, SdfWithConditionAnnotatesOnlyMatchingSvCondition) {
  SpecifyManager mgr;
  TimingCheckEntry m = MakeSv(TimingCheckKind::kSetup, "clk", "d",
                              SpecifyEdge::kNone, SpecifyEdge::kNone, "mode");
  m.limit = 1;
  mgr.AddTimingCheck(m);
  TimingCheckEntry nm = MakeSv(TimingCheckKind::kSetup, "clk", "d",
                               SpecifyEdge::kNone, SpecifyEdge::kNone, "!mode");
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

TEST(SdfTimingCheckMapping,
     BareSdfSetupholdMatchesAllSvSetupholdsRegardlessOfEdgeOrCondition) {
  SpecifyManager mgr;
  TimingCheckEntry a =
      MakeSv(TimingCheckKind::kSetuphold, "clk", "data", SpecifyEdge::kPosedge,
             SpecifyEdge::kNone, "mode");
  mgr.AddTimingCheck(a);
  TimingCheckEntry b =
      MakeSv(TimingCheckKind::kSetuphold, "clk", "data", SpecifyEdge::kNegedge,
             SpecifyEdge::kNone, "!mode");
  mgr.AddTimingCheck(b);
  TimingCheckEntry c =
      MakeSv(TimingCheckKind::kSetuphold, "clk", "data", SpecifyEdge::kEdge);
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

TEST(SdfTimingCheckMapping, SdfWithRefEdgeMatchesSvDespiteSvCondition) {
  SpecifyManager mgr;
  TimingCheckEntry sv =
      MakeSv(TimingCheckKind::kSetuphold, "clk", "data", SpecifyEdge::kPosedge,
             SpecifyEdge::kNone, "mode");
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

  EXPECT_EQ(mgr.GetTimingChecks()[0].condition, "mode");
}

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

TEST(SdfTimingCheckMapping,
     ParsedCondWrappedSetupholdAnnotatesNoneOfMismatchedSiblings) {
  SpecifyManager mgr;
  TimingCheckEntry mode_pos =
      MakeSv(TimingCheckKind::kSetuphold, "clk", "data", SpecifyEdge::kPosedge,
             SpecifyEdge::kNone, "mode");
  mode_pos.limit = 11;
  mode_pos.limit2 = 12;
  mgr.AddTimingCheck(mode_pos);
  TimingCheckEntry notmode_neg =
      MakeSv(TimingCheckKind::kSetuphold, "clk", "data", SpecifyEdge::kNegedge,
             SpecifyEdge::kNone, "!mode");
  notmode_neg.limit = 21;
  notmode_neg.limit2 = 22;
  mgr.AddTimingCheck(notmode_neg);
  TimingCheckEntry edge_only =
      MakeSv(TimingCheckKind::kSetuphold, "clk", "data", SpecifyEdge::kEdge);
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
    } else if (t.ref_edge == SpecifyEdge::kNegedge && t.condition == "!mode") {
      EXPECT_EQ(t.limit, 21u);
      EXPECT_EQ(t.limit2, 22u);
    } else if (t.ref_edge == SpecifyEdge::kEdge && t.condition.empty()) {
      EXPECT_EQ(t.limit, 31u);
      EXPECT_EQ(t.limit2, 32u);
    }
  }
}

}  // namespace
