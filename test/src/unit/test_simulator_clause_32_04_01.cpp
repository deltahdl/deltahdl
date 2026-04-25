#include <gtest/gtest.h>

#include <string>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// =============================================================================
// §32.4.1 — Mapping of SDF delay constructs to SystemVerilog declarations
// =============================================================================

// §32.4.1 body sentence 1: "When annotating DELAY constructs that are not
// interconnect delays..., the SDF annotator looks for specify paths where the
// names and conditions match." A bare (IOPATH src dst ...) carries no SDF
// condition, so the parser must record the absence of a condition explicitly
// rather than leaving the field uninitialised — otherwise the conditional/
// nonconditional dispatch in the annotator cannot tell the two cases apart.
TEST(SdfDelayMapping, BareIopathHasNoConditionAndIsNotIfnone) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH a y (10) (20))))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  ASSERT_EQ(file.cells[0].iopaths.size(), 1u);
  EXPECT_TRUE(file.cells[0].iopaths[0].condition.empty());
  EXPECT_FALSE(file.cells[0].iopaths[0].is_ifnone);
}

// §32.4.1 Table 32-1 row "(COND (IOPATH...) → Conditional specify path
// delays/pulse limits": a (COND <expr> (IOPATH ...)) wrapper carries a
// condition expression that shall reach the SdfIopath so the annotator can
// later compare it against the SystemVerilog `if (cond)` text.
TEST(SdfDelayMapping, CondIopathCarriesConditionText) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (COND mode (IOPATH a y (10) (20)))))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  ASSERT_EQ(file.cells[0].iopaths.size(), 1u);
  EXPECT_EQ(file.cells[0].iopaths[0].condition, "mode");
  EXPECT_FALSE(file.cells[0].iopaths[0].is_ifnone);
  EXPECT_EQ(file.cells[0].iopaths[0].src_port, "a");
  EXPECT_EQ(file.cells[0].iopaths[0].dst_port, "y");
  EXPECT_EQ(file.cells[0].iopaths[0].rise.typ_val, 10u);
  EXPECT_EQ(file.cells[0].iopaths[0].fall.typ_val, 20u);
}

// §32.4.1 Table 32-1 row "(CONDELSE (IOPATH...) → ifnone": the CONDELSE
// wrapper does not carry an explicit expression — its semantics are
// "ifnone", i.e. the SystemVerilog else-branch specify path. The parser
// flags the iopath with is_ifnone so the annotator can route it.
TEST(SdfDelayMapping, CondelseIopathSetsIfnoneFlag) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (CONDELSE (IOPATH a y (10) (20)))))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  ASSERT_EQ(file.cells[0].iopaths.size(), 1u);
  EXPECT_TRUE(file.cells[0].iopaths[0].is_ifnone);
  EXPECT_TRUE(file.cells[0].iopaths[0].condition.empty());
  EXPECT_EQ(file.cells[0].iopaths[0].src_port, "a");
  EXPECT_EQ(file.cells[0].iopaths[0].dst_port, "y");
}

// §32.4.1 sentence: "A nonconditional IOPATH delay between two ports shall
// annotate to all SystemVerilog specify paths between those same two ports."
// The manager pre-loads two specify paths between (a, y) — one guarded by
// `mode`, one by `!mode` — and then a bare IOPATH must update both.
TEST(SdfDelayMapping, NonconditionalIopathAnnotatesAllPathsBetweenSamePorts) {
  SpecifyManager mgr;
  PathDelay sv_then;
  sv_then.src_port = "a";
  sv_then.dst_port = "y";
  sv_then.condition = "mode";
  sv_then.delay_count = 1;
  sv_then.delays[0] = 1;
  mgr.AddPathDelay(sv_then);

  PathDelay sv_else;
  sv_else.src_port = "a";
  sv_else.dst_port = "y";
  sv_else.condition = "!mode";
  sv_else.delay_count = 1;
  sv_else.delays[0] = 2;
  mgr.AddPathDelay(sv_else);

  ASSERT_EQ(mgr.GetPathDelays().size(), 2u);

  SdfFile file;
  SdfCell cell;
  SdfIopath io;
  io.src_port = "a";
  io.dst_port = "y";
  io.rise.typ_val = 13;
  io.fall.typ_val = 17;
  cell.iopaths.push_back(io);
  file.cells.push_back(cell);

  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 2u);
  // Both pre-existing specify paths receive the new rise/fall, while their
  // own conditional identities survive — the annotator updates payload, not
  // the matched SV declaration's condition.
  for (const auto& pd : mgr.GetPathDelays()) {
    EXPECT_EQ(pd.src_port, "a");
    EXPECT_EQ(pd.dst_port, "y");
    EXPECT_EQ(pd.delays[0], 13u);
    EXPECT_EQ(pd.delays[1], 17u);
  }
  bool saw_then = false;
  bool saw_else = false;
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.condition == "mode") saw_then = true;
    if (pd.condition == "!mode") saw_else = true;
  }
  EXPECT_TRUE(saw_then);
  EXPECT_TRUE(saw_else);
}

// §32.4.1 sentence: "A conditional IOPATH delay between two ports shall
// annotate only to SystemVerilog specify paths between those same two ports
// with the same condition." The same two pre-loaded specify paths from above
// must this time receive the SDF update on the `mode` side only.
TEST(SdfDelayMapping, ConditionalIopathAnnotatesOnlyMatchingConditionPath) {
  SpecifyManager mgr;
  PathDelay sv_then;
  sv_then.src_port = "a";
  sv_then.dst_port = "y";
  sv_then.condition = "mode";
  sv_then.delay_count = 1;
  sv_then.delays[0] = 1;
  mgr.AddPathDelay(sv_then);

  PathDelay sv_else;
  sv_else.src_port = "a";
  sv_else.dst_port = "y";
  sv_else.condition = "!mode";
  sv_else.delay_count = 1;
  sv_else.delays[0] = 2;
  mgr.AddPathDelay(sv_else);

  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (COND mode (IOPATH a y (13) (17)))))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 2u);
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.condition == "mode") {
      EXPECT_EQ(pd.delays[0], 13u);
      EXPECT_EQ(pd.delays[1], 17u);
    } else if (pd.condition == "!mode") {
      // Untouched: the SDF condition `mode` does not match `!mode`, so the
      // pre-annotation value persists per §32.3 sentence 4.
      EXPECT_EQ(pd.delays[0], 2u);
    } else {
      ADD_FAILURE() << "unexpected condition: " << pd.condition;
    }
  }
}

// §32.4.1 Table 32-1 "(CONDELSE (IOPATH...) → ifnone": a CONDELSE-wrapped
// IOPATH may only annotate to the ifnone specify path between the two named
// ports. A sibling conditional path between the same two ports keeps its
// pre-annotation value.
TEST(SdfDelayMapping, CondelseIopathAnnotatesOnlyIfnonePath) {
  SpecifyManager mgr;
  PathDelay sv_cond;
  sv_cond.src_port = "a";
  sv_cond.dst_port = "y";
  sv_cond.condition = "mode";
  sv_cond.delay_count = 1;
  sv_cond.delays[0] = 1;
  mgr.AddPathDelay(sv_cond);

  PathDelay sv_ifnone;
  sv_ifnone.src_port = "a";
  sv_ifnone.dst_port = "y";
  sv_ifnone.is_ifnone = true;
  sv_ifnone.delay_count = 1;
  sv_ifnone.delays[0] = 2;
  mgr.AddPathDelay(sv_ifnone);

  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (CONDELSE (IOPATH a y (13) (17)))))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 2u);
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.is_ifnone) {
      EXPECT_EQ(pd.delays[0], 13u);
      EXPECT_EQ(pd.delays[1], 17u);
    } else if (pd.condition == "mode") {
      EXPECT_EQ(pd.delays[0], 1u);
    } else {
      ADD_FAILURE() << "unexpected pd state";
    }
  }
}

// §32.4.1 closure: once COND/CONDELSE-wrapped IOPATHs are annotated by §32.4.1,
// they are no longer "data the annotator was unable to annotate" under §32.3
// sentence 1, so a SDF file consisting only of such constructs produces no
// warnings.
TEST(SdfDelayMapping, CondAndCondelseIopathProduceNoUnannotatableWarnings) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (COND mode (IOPATH a y (10) (20)))
            (CONDELSE (IOPATH a y (5) (6)))
          )
        )
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  SpecifyManager mgr;
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
  EXPECT_TRUE(result.warnings.empty());
}

// §32.4.1 Table 32-1 COND IOPATH row, min/typ/max edge: a COND wrapper must
// not interfere with delay-value extraction underneath it. Pinning the typ
// column through the wrapper guards against a parser regression where the
// COND branch silently consumes the rise/fall triplets.
TEST(SdfDelayMapping, CondIopathPreservesMinTypMaxDelaySelection) {
  SpecifyManager mgr;
  PathDelay sv;
  sv.src_port = "a";
  sv.dst_port = "y";
  sv.condition = "mode";
  sv.delay_count = 1;
  sv.delays[0] = 0;
  mgr.AddPathDelay(sv);

  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (COND mode (IOPATH a y (1:7:9) (2:8:11)))))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  EXPECT_EQ(mgr.GetPathDelays()[0].condition, "mode");
  EXPECT_EQ(mgr.GetPathDelays()[0].delays[0], 7u);
  EXPECT_EQ(mgr.GetPathDelays()[0].delays[1], 8u);
}

// §32.4.1 conditional shall rule, multiple-sibling edge: when two SV specify
// paths between the same two ports carry distinct conditions, two SDF COND
// IOPATHs must each land on their own sibling. The annotator's condition
// matching has to be exact — neither SDF entry may bleed onto the other's
// declaration.
TEST(SdfDelayMapping, MultipleCondIopathsAnnotateRespectiveSiblings) {
  SpecifyManager mgr;
  PathDelay sv_m1;
  sv_m1.src_port = "a";
  sv_m1.dst_port = "y";
  sv_m1.condition = "m1";
  sv_m1.delay_count = 1;
  sv_m1.delays[0] = 0;
  mgr.AddPathDelay(sv_m1);

  PathDelay sv_m2;
  sv_m2.src_port = "a";
  sv_m2.dst_port = "y";
  sv_m2.condition = "m2";
  sv_m2.delay_count = 1;
  sv_m2.delays[0] = 0;
  mgr.AddPathDelay(sv_m2);

  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (COND m1 (IOPATH a y (10) (20)))
            (COND m2 (IOPATH a y (30) (40)))
          )
        )
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 2u);
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.condition == "m1") {
      EXPECT_EQ(pd.delays[0], 10u);
      EXPECT_EQ(pd.delays[1], 20u);
    } else if (pd.condition == "m2") {
      EXPECT_EQ(pd.delays[0], 30u);
      EXPECT_EQ(pd.delays[1], 40u);
    } else {
      ADD_FAILURE() << "unexpected condition: " << pd.condition;
    }
  }
}

// §32.4.1 nonconditional shall rule, ifnone-sibling edge: an ifnone path is
// still a specify path between the two named ports, so a nonconditional
// IOPATH must update its delays alongside a conditional sibling. The SV
// declaration's ifnone identity survives the update — only the payload
// changes.
TEST(SdfDelayMapping, NonconditionalIopathUpdatesIfnoneSiblingToo) {
  SpecifyManager mgr;
  PathDelay sv_cond;
  sv_cond.src_port = "a";
  sv_cond.dst_port = "y";
  sv_cond.condition = "mode";
  sv_cond.delay_count = 1;
  sv_cond.delays[0] = 0;
  mgr.AddPathDelay(sv_cond);

  PathDelay sv_ifnone;
  sv_ifnone.src_port = "a";
  sv_ifnone.dst_port = "y";
  sv_ifnone.is_ifnone = true;
  sv_ifnone.delay_count = 1;
  sv_ifnone.delays[0] = 0;
  mgr.AddPathDelay(sv_ifnone);

  SdfFile file;
  SdfCell cell;
  SdfIopath io;
  io.src_port = "a";
  io.dst_port = "y";
  io.rise.typ_val = 7;
  io.fall.typ_val = 9;
  cell.iopaths.push_back(io);
  file.cells.push_back(cell);

  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 2u);
  bool saw_ifnone_with_payload = false;
  bool saw_cond_with_payload = false;
  for (const auto& pd : mgr.GetPathDelays()) {
    EXPECT_EQ(pd.delays[0], 7u);
    EXPECT_EQ(pd.delays[1], 9u);
    if (pd.is_ifnone) saw_ifnone_with_payload = true;
    if (pd.condition == "mode") saw_cond_with_payload = true;
  }
  EXPECT_TRUE(saw_ifnone_with_payload);
  EXPECT_TRUE(saw_cond_with_payload);
}

// §32.4.1 body sentence 2: when annotating TIMINGCHECK constructs, the
// annotator looks for timing checks of the same type where names AND
// conditions match. Two stored timing checks that share kind/signals/edges
// but carry different SystemVerilog `&&&` conditions must remain distinct
// backannotation targets — an incoming entry with one condition value
// updates only the matching sibling, leaving the other untouched.
TEST(SdfDelayMapping, TimingCheckMatchingDistinguishesByCondition) {
  SpecifyManager mgr;
  TimingCheckEntry tc_then;
  tc_then.kind = TimingCheckKind::kSetup;
  tc_then.ref_signal = "clk";
  tc_then.data_signal = "d";
  tc_then.condition = "mode";
  tc_then.limit = 1;
  mgr.AddTimingCheck(tc_then);

  TimingCheckEntry tc_else;
  tc_else.kind = TimingCheckKind::kSetup;
  tc_else.ref_signal = "clk";
  tc_else.data_signal = "d";
  tc_else.condition = "!mode";
  tc_else.limit = 2;
  mgr.AddTimingCheck(tc_else);

  TimingCheckEntry update;
  update.kind = TimingCheckKind::kSetup;
  update.ref_signal = "clk";
  update.data_signal = "d";
  update.condition = "mode";
  update.limit = 99;
  mgr.AddTimingCheck(update);

  ASSERT_EQ(mgr.GetTimingChecks().size(), 2u);
  for (const auto& t : mgr.GetTimingChecks()) {
    if (t.condition == "mode") {
      EXPECT_EQ(t.limit, 99u);
    } else if (t.condition == "!mode") {
      EXPECT_EQ(t.limit, 2u);
    } else {
      ADD_FAILURE() << "unexpected condition: " << t.condition;
    }
  }
}

// §32.4.1 Table 32-1 PATHPULSE row: an absolute (PATHPULSE src dst reject
// error) construct annotates the per-transition reject and error limits of
// every PathDelay between the named ports. The path's propagation delays
// are not touched — only the §30.7 pulse-filter limits.
TEST(SdfDelayMapping, PathpulseAnnotatesAbsolutePulseLimits) {
  SpecifyManager mgr;
  PathDelay pd;
  pd.src_port = "a";
  pd.dst_port = "y";
  pd.delay_count = 1;
  pd.delays[0] = 50;
  pd.reject_limit[0] = 50;
  pd.error_limit[0] = 50;
  mgr.AddPathDelay(pd);

  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (PATHPULSE a y (10) (20))))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_TRUE(result.warnings.empty());
  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  EXPECT_EQ(mgr.GetPathDelays()[0].delays[0], 50u);
  EXPECT_EQ(mgr.GetPathDelays()[0].reject_limit[0], 10u);
  EXPECT_EQ(mgr.GetPathDelays()[0].error_limit[0], 20u);
}

// §32.4.1 Table 32-1 PATHPULSE row, single-value form: when only the reject
// limit is supplied, the X band collapses to zero — error_limit mirrors
// reject_limit, matching the §30.7.3 single-value rule that this row
// inherits.
TEST(SdfDelayMapping, PathpulseSingleValueCollapsesXBand) {
  SpecifyManager mgr;
  PathDelay pd;
  pd.src_port = "a";
  pd.dst_port = "y";
  pd.delay_count = 1;
  pd.delays[0] = 50;
  pd.reject_limit[0] = 50;
  pd.error_limit[0] = 50;
  mgr.AddPathDelay(pd);

  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (PATHPULSE a y (8))))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_EQ(mgr.GetPathDelays()[0].reject_limit[0], 8u);
  EXPECT_EQ(mgr.GetPathDelays()[0].error_limit[0], 8u);
}

// §32.4.1 Table 32-1 PATHPULSE row applied across siblings: the table maps
// PATHPULSE to "conditional and nonconditional specify path pulse limits",
// so a single SDF entry must fan out across every PathDelay between the
// two named ports — both conditional siblings and any ifnone sibling.
TEST(SdfDelayMapping, PathpulseAnnotatesAllPathsBetweenSamePorts) {
  SpecifyManager mgr;
  PathDelay sv_then;
  sv_then.src_port = "a";
  sv_then.dst_port = "y";
  sv_then.condition = "mode";
  sv_then.delay_count = 1;
  sv_then.delays[0] = 30;
  mgr.AddPathDelay(sv_then);

  PathDelay sv_else;
  sv_else.src_port = "a";
  sv_else.dst_port = "y";
  sv_else.condition = "!mode";
  sv_else.delay_count = 1;
  sv_else.delays[0] = 40;
  mgr.AddPathDelay(sv_else);

  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (PATHPULSE a y (5) (15))))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 2u);
  for (const auto& pd : mgr.GetPathDelays()) {
    EXPECT_EQ(pd.reject_limit[0], 5u);
    EXPECT_EQ(pd.error_limit[0], 15u);
  }
}

// §32.4.1 Table 32-1 PATHPULSEPERCENT row: percentages scale each PathDelay's
// own delay value into the matching reject_limit / error_limit slot. With a
// 10 ns path delay and a 25%/75% PATHPULSEPERCENT entry, reject becomes
// 2 ns and error becomes 7 ns.
TEST(SdfDelayMapping, PathpulsepercentScalesFromPathDelay) {
  SpecifyManager mgr;
  PathDelay pd;
  pd.src_port = "a";
  pd.dst_port = "y";
  pd.delay_count = 1;
  pd.delays[0] = 10;
  pd.reject_limit[0] = 10;
  pd.error_limit[0] = 10;
  mgr.AddPathDelay(pd);

  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (PATHPULSEPERCENT a y (25) (75))))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_EQ(mgr.GetPathDelays()[0].delays[0], 10u);
  EXPECT_EQ(mgr.GetPathDelays()[0].reject_limit[0], 2u);
  EXPECT_EQ(mgr.GetPathDelays()[0].error_limit[0], 7u);
}

// §32.4.1 Table 32-1 RETAIN rows: the table allows the simulator to ignore
// a (RETAIN ...) qualifier on an IOPATH. "Ignore" must mean syntactic
// transparency — the surrounding rise/fall delay-value triplets must still
// land in the correct slots regardless of whether RETAIN is present.
TEST(SdfDelayMapping, IopathRetainQualifierIsParsedAndIgnored) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH a y (RETAIN (3) (4)) (10) (20))))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  ASSERT_EQ(file.cells[0].iopaths.size(), 1u);
  EXPECT_EQ(file.cells[0].iopaths[0].src_port, "a");
  EXPECT_EQ(file.cells[0].iopaths[0].dst_port, "y");
  EXPECT_EQ(file.cells[0].iopaths[0].rise.typ_val, 10u);
  EXPECT_EQ(file.cells[0].iopaths[0].fall.typ_val, 20u);
}

// §32.4.1 Table 32-1 RETAIN rows under COND: ignoring RETAIN must compose
// with the COND wrapper — the condition still reaches the iopath while the
// retain block is silently consumed.
TEST(SdfDelayMapping, CondIopathWithRetainIgnoresRetainAndKeepsCondition) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (COND mode (IOPATH a y (RETAIN (1) (2)) (10) (20)))
          )
        )
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  ASSERT_EQ(file.cells[0].iopaths.size(), 1u);
  EXPECT_EQ(file.cells[0].iopaths[0].condition, "mode");
  EXPECT_EQ(file.cells[0].iopaths[0].rise.typ_val, 10u);
  EXPECT_EQ(file.cells[0].iopaths[0].fall.typ_val, 20u);
}

// §32.4.1 Table 32-1 RETAIN rows under CONDELSE: same composition with the
// ifnone routing — RETAIN drops away cleanly.
TEST(SdfDelayMapping, CondelseIopathWithRetainIgnoresRetainAndKeepsIfnone) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (CONDELSE (IOPATH a y (RETAIN (1)) (10) (20)))
          )
        )
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  ASSERT_EQ(file.cells[0].iopaths.size(), 1u);
  EXPECT_TRUE(file.cells[0].iopaths[0].is_ifnone);
  EXPECT_EQ(file.cells[0].iopaths[0].rise.typ_val, 10u);
  EXPECT_EQ(file.cells[0].iopaths[0].fall.typ_val, 20u);
}

// §32.4.1 conditional shall rule, ifnone-exclusion edge: a (COND mode
// (IOPATH a y ...)) names a same-condition match. An ifnone sibling between
// the same two ports has no condition — its conditional shape is "ifnone",
// not "mode" — so it must not be touched. The annotator instead leaves the
// ifnone payload at its prebackannotation value and appends the new
// conditional entry.
TEST(SdfDelayMapping, ConditionalIopathDoesNotAnnotateIfnoneSibling) {
  SpecifyManager mgr;
  PathDelay sv_ifnone;
  sv_ifnone.src_port = "a";
  sv_ifnone.dst_port = "y";
  sv_ifnone.is_ifnone = true;
  sv_ifnone.delay_count = 1;
  sv_ifnone.delays[0] = 99;
  mgr.AddPathDelay(sv_ifnone);

  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (COND mode (IOPATH a y (4) (5)))))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  bool saw_untouched_ifnone = false;
  bool saw_new_conditional = false;
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.is_ifnone) {
      EXPECT_EQ(pd.delays[0], 99u);
      saw_untouched_ifnone = true;
    } else if (pd.condition == "mode") {
      EXPECT_EQ(pd.delays[0], 4u);
      EXPECT_EQ(pd.delays[1], 5u);
      saw_new_conditional = true;
    }
  }
  EXPECT_TRUE(saw_untouched_ifnone);
  EXPECT_TRUE(saw_new_conditional);
}

}  // namespace
