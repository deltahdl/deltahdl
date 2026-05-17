#include <gtest/gtest.h>

#include <string>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

TEST(SdfAnnotator, WarnsForDataItIsUnableToAnnotate) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (PATHPULSE a y (3) (5))
          )
        )
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));

  SpecifyManager mgr;
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_FALSE(result.warnings.empty());
}

TEST(SdfAnnotator, NoWarningsForFullySupportedFile) {
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

  SpecifyManager mgr;
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_TRUE(result.warnings.empty());
}

TEST(SdfAnnotator, TimingenvIsIgnoredWithoutWarnings) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (TIMINGENV
        (PATHCONSTRAINT a b (10))
      )
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH a y (10) (20))))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));

  SpecifyManager mgr;
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_TRUE(mgr.HasPathDelay("a", "y"));
}

TEST(SdfAnnotator, UnspecifiedPathDelayIsPreserved) {
  SpecifyManager mgr;
  PathDelay pd;
  pd.src_port = "a";
  pd.dst_port = "y";
  pd.delay_count = 1;
  pd.delays[0] = 42;
  mgr.AddPathDelay(pd);

  SdfFile file;
  SdfCell cell;
  SdfIopath io;
  io.src_port = "b";
  io.dst_port = "z";
  io.rise.typ_val = 7;
  io.fall.typ_val = 8;
  cell.iopaths.push_back(io);
  file.cells.push_back(cell);

  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 42u);
}

TEST(SdfAnnotator, EachUnannotatableConstructProducesItsOwnWarning) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (PATHPULSE a y (3) (5))
            (DEVICE u1 (10) (20))
          )
        )
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));

  SpecifyManager mgr;
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_GE(result.warnings.size(), 2u);
}

TEST(SdfAnnotator, EmptySdfPreservesPopulatedManager) {
  SpecifyManager mgr;

  PathDelay pd;
  pd.src_port = "a";
  pd.dst_port = "y";
  pd.delay_count = 1;
  pd.delays[0] = 11;
  mgr.AddPathDelay(pd);

  SpecparamValue sp;
  sp.name = "tHold";
  sp.value = 33;
  mgr.SetSpecparamValue(sp);

  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetup;
  tc.ref_signal = "clk";
  tc.data_signal = "d";
  tc.limit = 55;
  mgr.AddTimingCheck(tc);

  InterconnectDelay ic;
  ic.src_port = "u1.q";
  ic.dst_port = "u2.d";
  ic.rise = 7;
  ic.fall = 9;
  mgr.AddInterconnectDelay(ic);

  SdfFile empty_file;
  SdfAnnotationResult result =
      AnnotateSdfToManager(empty_file, mgr, SdfMtm::kTypical);

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 11u);
  ASSERT_EQ(mgr.GetSpecparamValues().size(), 1u);
  EXPECT_EQ(mgr.GetSpecparamValues()[0].value, 33u);
  ASSERT_EQ(mgr.TimingCheckCount(), 1u);
  EXPECT_EQ(mgr.GetTimingChecks()[0].limit, 55u);
  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  EXPECT_EQ(mgr.GetInterconnectDelays()[0].rise, 7u);
}

TEST(SdfAnnotator, SilentIgnoredWarnedAndAnnotatedAllCoexist) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "x";
  pre.dst_port = "w";
  pre.delay_count = 1;
  pre.delays[0] = 99;
  mgr.AddPathDelay(pre);

  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (TIMINGENV
        (PATHCONSTRAINT a b (5))
      )
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (PATHPULSE a y (3) (5))
            (IOPATH b z (1) (2))
          )
        )
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));

  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_EQ(result.warnings.size(), 1u);
  EXPECT_TRUE(mgr.HasPathDelay("b", "z"));
  EXPECT_EQ(mgr.GetPathDelay("x", "w"), 99u);
}

}
