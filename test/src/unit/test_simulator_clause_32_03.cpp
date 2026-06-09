#include <gtest/gtest.h>

#include <string>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// S1: the annotator shall warn for any data it is unable to annotate, and the
// warning is per construct -- each unannotatable entry produces its own
// message. DEVICE is a delay construct this annotator does not support, so it
// falls through ParseDelaySection's else branch into file.unannotatable; two of
// them must yield two warnings (subsumes the single-warning existence case).
TEST(SdfAnnotator, EachUnannotatableConstructProducesItsOwnWarning) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (DEVICE u1 (10) (20))
            (DEVICE u2 (30) (40))
          )
        )
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));

  SpecifyManager mgr;
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_EQ(result.warnings.size(), 2u);
}

// S2: constructs unrelated to SystemVerilog timing (the TIMINGENV section being
// the canonical example) are skipped silently -- no warning is issued -- while
// the supported constructs alongside them are still annotated. A clean zero
// warning count proves both that TIMINGENV contributes nothing and that the
// supported IOPATH does not over-warn.
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

// S2 edge case: the unrelated section sits inside a CELL (TIMINGENV's actual
// home in an SDF file) rather than at the top level. This exercises the
// cell-level skip path, distinct from the file-level one above: the TIMINGENV
// section is dropped silently while the cell's own DELAY is still annotated.
TEST(SdfAnnotator, TimingenvInsideCellIsIgnoredWithoutWarnings) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (TIMINGENV
          (PATHCONSTRAINT a b (10))
        )
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

// S3: any timing value the SDF file does not provide must keep its
// prebackannotation value. An empty SDF provides nothing, so every category of
// value already in the manager -- path delay, specparam, timing check, and
// interconnect delay -- must be left exactly as it was.
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

// Integration of all three rules at once: an unrelated TIMINGENV section is
// ignored silently (S2), an unsupported DEVICE construct warns (S1), a
// supported IOPATH is annotated, and a prebackannotation path delay the SDF
// never mentions is preserved (S3). The exact warning count of one proves the
// silent-ignored and annotated constructs add no spurious warnings.
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
            (DEVICE u1 (3) (5))
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

}  // namespace
