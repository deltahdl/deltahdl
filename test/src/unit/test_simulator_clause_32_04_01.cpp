#include <gtest/gtest.h>

#include <string>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

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

      EXPECT_EQ(pd.delays[0], 2u);
    } else {
      ADD_FAILURE() << "unexpected condition: " << pd.condition;
    }
  }
}

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

}
