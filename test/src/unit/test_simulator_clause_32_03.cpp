#include <gtest/gtest.h>

#include <string>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// §32.3 sentence 1: "It shall issue a warning for any data it is unable
// to annotate." A COND-qualified IOPATH lives inside the DELAY section of
// a CELL — clearly timing data — but the parser does not yet decode it,
// so the annotator must surface a warning rather than dropping it on the
// floor.
TEST(SdfAnnotator, WarnsForDataItIsUnableToAnnotate) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (COND mode (IOPATH a y (10) (20)))
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

// §32.3: the converse of sentence 1 — when every construct in the SDF
// file is one the annotator handles, no warnings are issued.
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

// §32.3 sentence 3: "All constructs unrelated to SystemVerilog timing
// shall be ignored without any warnings issued." The TIMINGENV section
// is the LRM's named example.
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

// §32.3 sentence 4: "Any SystemVerilog timing value for which the SDF
// file does not provide a value shall not be modified during the
// backannotation process, and its prebackannotation value shall be
// unchanged." A path delay loaded into the manager before annotation
// must survive an annotation pass that names a different path.
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

// §32.3 sentence 1 (quantifier edge case): "any data" — when several
// distinct unannotatable constructs share a single DELAY section, each
// must produce its own warning rather than collapsing to one.
TEST(SdfAnnotator, EachUnannotatableConstructProducesItsOwnWarning) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (COND mode (IOPATH a y (10) (20)))
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

  EXPECT_GE(result.warnings.size(), 2u);
}

// §32.3 sentence 4 edge case: an SDF file with no cells (so no value
// updates whatsoever) leaves a populated SpecifyManager fully intact
// across all four §32.2 categories.
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

// §32.3 integration: a single SDF file mixes a silent TIMINGENV section
// (sentence 2), an unannotatable construct (sentence 1), an annotated
// IOPATH (the happy path), while the manager already holds a
// prebackannotation path delay the file does not name (sentence 4). All
// three rules must hold simultaneously and independently.
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
            (COND mode (IOPATH a y (10) (20)))
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
