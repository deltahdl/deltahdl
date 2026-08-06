#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "fixture_specify_manager.h"
#include "simulator/evaluation.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// --- Prebackannotation values driven from real source syntax ---------------
// §32.3's third rule is about what a SystemVerilog timing value held BEFORE
// backannotation, so the value has to arrive the way a design actually
// produces it. BuildSpecifyFromSource parses and elaborates a module, runs it,
// and then fills a SpecifyManager from that module's specify block using the
// production builders: a §6.20.5 specparam declaration, §30.5 module path
// assignments, and a §31.2 timing check declaration. Nothing in the manager is
// hand-assembled except the interconnect delays, which SystemVerilog has no
// declaration syntax for at all.
bool BuildSpecifyFromSource(const std::string& src, SimFixture& f,
                            SpecifyManager& mgr) {
  auto* cu = RunModuleSource(src, f);
  if (cu == nullptr) return false;
  for (auto* mod : cu->modules) {
    RegisterPathDelays(*mod, f, mgr);
    RegisterTimingChecks(*mod, f, mgr);
    RegisterSpecparamValues(*mod, f, mgr);
  }
  return true;
}

// The design every source-driven test below backannotates onto. It declares
// values in each of the three categories SystemVerilog can express, and two of
// each kind that can have siblings, so a file that provides a value for one can
// be checked against the one it left alone: a specparam (11), two module path
// delays (21 and 31), and two timing constraints (setup 41, hold 51). Every
// number is distinct, so untouched is never confusable with overwritten.
const char* const kDesign =
    "module t(input a, input b, input clk, input d, output y, output z);\n"
    "  reg ntf;\n"
    "  specify\n"
    "    specparam tRise = 11;\n"
    "    (a => y) = 21;\n"
    "    (b => z) = 31;\n"
    "    $setup(posedge clk, d, 41, ntf);\n"
    "    $hold(posedge clk, d, 51, ntf);\n"
    "  endspecify\n"
    "endmodule\n";

// Reads back the limit of the first declared check of the given kind, or a
// sentinel when the manager carries none.
uint64_t LimitOf(const SpecifyManager& mgr, TimingCheckKind kind) {
  for (const auto& tc : mgr.GetTimingChecks()) {
    if (tc.kind == kind) return tc.limit;
  }
  return ~0ull;
}

// Reads back the value of the named specparam, or a sentinel when the manager
// does not carry one by that name.
uint64_t SpecparamOf(const SpecifyManager& mgr, const std::string& name) {
  for (const auto& sp : mgr.GetSpecparamValues()) {
    if (sp.name == name) return sp.value;
  }
  return ~0ull;
}

// Reads back a whole declared check of the given kind, for the tests that have
// to compare more of it than the first limit. Yields a default-built entry when
// the manager carries no check of that kind.
TimingCheckEntry CheckOfKind(const SpecifyManager& mgr, TimingCheckKind kind) {
  for (const auto& tc : mgr.GetTimingChecks()) {
    if (tc.kind == kind) return tc;
  }
  return TimingCheckEntry{};
}

// Reads back a whole module path delay by its endpoints, so a test can snapshot
// one before backannotation and compare every transition slot afterwards.
PathDelay PathBetween(const SpecifyManager& mgr, std::string_view src,
                      std::string_view dst) {
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.src_port == src && pd.dst_port == dst) return pd;
  }
  return PathDelay{};
}

// Parses |sdf| and annotates it onto a manager that is already populated, for
// the tests that snapshot prebackannotation state before applying the file.
SdfAnnotationResult AnnotateFileOnto(const std::string& sdf,
                                     SpecifyManager& mgr) {
  SdfFile file;
  EXPECT_TRUE(ParseSdf(sdf, file));
  return AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
}

// Parses |sdf|, annotates it onto a manager built from kDesign, and returns the
// warnings. Shared by the tests whose subject is what the annotator did NOT
// touch: each caller then asserts on the manager it passed in.
SdfAnnotationResult AnnotateOntoDesign(const std::string& sdf, SimFixture& f,
                                       SpecifyManager& mgr) {
  EXPECT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));
  return AnnotateFileOnto(sdf, mgr);
}

// ---------------------------------------------------------------------------
// C1: a warning for any data the annotator cannot annotate.
// ---------------------------------------------------------------------------

// C1: the warning is per construct -- each unannotatable entry produces its own
// message. DEVICE is a delay construct this annotator does not support, so it
// falls through the delay-section dispatch into the unannotatable list; two of
// them must yield two warnings (subsuming the single-warning existence case).
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

// C1, second input form: a conditioned delay entry. The annotator handles COND
// only when it wraps an IOPATH; wrapping anything else -- here an INTERCONNECT
// -- makes it data it cannot take in, so it warns instead of annotating.
TEST(SdfAnnotator, CondWrappingNonIopathWarns) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (COND mode (INTERCONNECT u1.q u2.d (10) (20)))
          )
        )
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));

  SpecifyManager mgr;
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("COND"), std::string::npos);
  EXPECT_TRUE(mgr.GetInterconnectDelays().empty());
}

// C1, third input form: the ifnone counterpart of the case above. CONDELSE also
// only carries an IOPATH; anything else warns and annotates nothing.
TEST(SdfAnnotator, CondElseWrappingNonIopathWarns) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (CONDELSE (INTERCONNECT u1.q u2.d (10) (20)))
          )
        )
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));

  SpecifyManager mgr;
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("CONDELSE"), std::string::npos);
  EXPECT_TRUE(mgr.GetInterconnectDelays().empty());
}

// C1, fourth input form: the specparam-carrying section. A LABEL section states
// up front whether its values replace or add to what is there; a leading
// keyword that is neither leaves the annotator unable to place the values, so
// it warns and no specparam is written.
TEST(SdfAnnotator, LabelWithUnknownModeWarnsAndWritesNoSpecparam) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (LABEL (SOMEMODE (tRise 77)))
      )
    )
  )",
                                   f, mgr);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("LABEL"), std::string::npos);
  // The declared specparam is untouched and no stray one was created.
  EXPECT_EQ(SpecparamOf(mgr, "tRise"), 11u);
  EXPECT_EQ(mgr.GetSpecparamValues().size(), 1u);
}

// C1, fifth input form: an entry of a TIMINGCHECK section whose keyword this
// annotator does not know. Everything in that section is timing data, so an
// unrecognized entry is unannotatable and must warn -- and, because C3 forbids
// touching a value the file did not provide, the declared $setup limit has to
// survive it rather than being overwritten by a guessed check type.
TEST(SdfAnnotator, UnknownTimingCheckKeywordWarnsAndLeavesCheckAlone) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (TIMINGCHECK (NOSUCHCHECK d (posedge clk) (5)))
      )
    )
  )",
                                   f, mgr);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("NOSUCHCHECK"), std::string::npos);
  ASSERT_EQ(mgr.TimingCheckCount(), 2u);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kSetup), 41u);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kHold), 51u);
}

// C1, sixth input form: data that parses cleanly and names a construct the
// annotator fully supports, but that matches nothing in the design. The file
// hands over a setup constraint between signals no declared check uses, so the
// annotator understood the value yet had nowhere to put it -- exactly the case
// the warning requirement is for. Dropping it in silence would leave the file's
// author believing the constraint took effect. The declared checks are also
// left as they were, since this file provided nothing for them (C3).
//
// Why the match failed is not this subclause's business: whether the signal
// names, the edge, or the check kind is what differs, §32.3 asks for the same
// warning, so one representative mismatch stands for all of them.
TEST(SdfAnnotator, TimingCheckMatchingNoDeclarationWarns) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (TIMINGCHECK (SETUP b (posedge a) (5)))
      )
    )
  )",
                                   f, mgr);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("SETUP"), std::string::npos);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kSetup), 41u);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kHold), 51u);
}

// C1, seventh input form: the keyword that opens a DELAY section body. It
// selects how the delays inside are applied; one it does not recognize makes
// the whole section unannotatable, so it warns -- and the IOPATH nested inside
// must NOT be applied, since applying it would pick an arbitrary mode for
// values the file never asked to be applied that way.
TEST(SdfAnnotator, UnknownDelaySectionModeWarnsAndAnnotatesNothing) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (DELAY (SOMEMODE (IOPATH a y (7) (7))))
      )
    )
  )",
                                   f, mgr);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("SOMEMODE"), std::string::npos);
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 21u);  // declared value survives
}

// C1, eighth input form: a sub-spec nested inside a construct the annotator
// does handle. A retain spec says how long an output holds its old value after
// an input changes -- propagation timing for the path being read, not
// information from outside the simulator's concern -- but SystemVerilog has
// nowhere to record it. So it warns, while the enclosing IOPATH's own delays
// still land: partial data is applied as far as it goes, and only the part with
// no home is reported.
TEST(SdfAnnotator, IopathRetainSubSpecWarnsWhileItsDelaysStillAnnotate) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH a y (RETAIN (3) (4)) (7) (7))))
      )
    )
  )",
                                   f, mgr);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("RETAIN"), std::string::npos);
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 7u);   // the IOPATH itself did land
  EXPECT_EQ(mgr.GetPathDelay("b", "z"), 31u);  // and nothing else moved
}

// C1 rejecting form, across every category the annotator does support: a file
// whose delay, interconnect, timing check, and specparam constructs are all
// recognized draws no warning at all. Without this, an annotator that warned
// indiscriminately would still pass the accepting tests above. It is also the
// reachability proof for the two accepting timing check tests: the same SETUP
// section they use, written with a keyword the annotator knows and signals a
// declaration uses, does land its value. The declared hold constraint the file
// says nothing about keeps its own limit, which is C3 within a single category.
TEST(SdfAnnotator, FullySupportedFileWarnsNothing) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (IOPATH a y (7) (7))
            (INTERCONNECT u1.q u2.d (2) (3))
          )
        )
        (TIMINGCHECK (SETUP d (posedge clk) (5)))
        (LABEL (ABSOLUTE (tRise 9)))
      )
    )
  )",
                                   f, mgr);

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 7u);
  EXPECT_EQ(SpecparamOf(mgr, "tRise"), 9u);
  ASSERT_EQ(mgr.TimingCheckCount(), 2u);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kSetup), 5u);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kHold), 51u);
  EXPECT_EQ(mgr.GetInterconnectDelays().size(), 1u);
}

// ---------------------------------------------------------------------------
// C2: constructs unrelated to SystemVerilog timing are dropped in silence.
// ---------------------------------------------------------------------------

// C2: the canonical unrelated construct is the TIMINGENV section, and here it
// sits at the top level of the file. It is skipped without a warning while the
// supported IOPATH alongside it is still annotated. A clean zero warning count
// proves both that TIMINGENV contributes nothing and that the IOPATH does not
// over-warn.
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

// C2, second syntactic position: the unrelated section sits inside a CELL,
// which is TIMINGENV's actual home in an SDF file. This exercises the
// cell-level skip path, distinct from the file-level one above: the section is
// dropped silently while the cell's own DELAY is still annotated.
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

// C2, third input form: the file header. Date, vendor, program, tool version,
// hierarchy divider, operating conditions, and timescale all describe how the
// file was produced rather than any SystemVerilog timing value, so every one of
// them is dropped in silence while the IOPATH that follows is annotated.
TEST(SdfAnnotator, HeaderConstructsAreIgnoredWithoutWarnings) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (SDFVERSION "3.0")
      (DESIGN "t")
      (DATE "Tuesday")
      (VENDOR "acme")
      (PROGRAM "delaycalc")
      (VERSION "1.2")
      (DIVIDER .)
      (VOLTAGE 1.8:1.8:1.8)
      (PROCESS "typical")
      (TEMPERATURE 25:25:25)
      (TIMESCALE 1ns)
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
  EXPECT_EQ(file.version, "3.0");
  EXPECT_TRUE(mgr.HasPathDelay("a", "y"));
}

// ---------------------------------------------------------------------------
// C3: a timing value the file does not provide keeps its prebackannotation
// value.
// ---------------------------------------------------------------------------

// C3, driven end to end from source: the file provides a value for exactly one
// of the design's four declared timing values. The a=>y path delay changes, and
// the other three -- the second module path, the specparam, and the $setup
// constraint -- all keep the value their declarations gave them. Annotating the
// one path is what makes the other three assertions meaningful: a do-nothing
// annotator would fail the first.
TEST(SdfAnnotator, PartialSdfLeavesUnmentionedDeclaredValuesUnchanged) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH a y (7) (7))))
      )
    )
  )",
                                   f, mgr);

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 7u);   // provided -> replaced
  EXPECT_EQ(mgr.GetPathDelay("b", "z"), 31u);  // not provided -> unchanged
  EXPECT_EQ(SpecparamOf(mgr, "tRise"), 11u);
  ASSERT_EQ(mgr.TimingCheckCount(), 2u);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kSetup), 41u);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kHold), 51u);
}

// C3 at the other extreme: a file that provides no timing value whatsoever --
// only header fields and an unrelated TIMINGENV section -- leaves every
// declared value exactly as the source wrote it, and says nothing while doing
// so (C2).
TEST(SdfAnnotator, ValuelessSdfLeavesEveryDeclaredValueUnchanged) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(R"(
    (DELAYFILE
      (SDFVERSION "3.0")
      (DESIGN "t")
      (TIMINGENV
        (PATHCONSTRAINT a b (10))
      )
    )
  )",
                                   f, mgr);

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 21u);
  EXPECT_EQ(mgr.GetPathDelay("b", "z"), 31u);
  EXPECT_EQ(SpecparamOf(mgr, "tRise"), 11u);
  ASSERT_EQ(mgr.TimingCheckCount(), 2u);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kSetup), 41u);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kHold), 51u);
}

// C3 for the one category SystemVerilog has no declaration syntax for.
// Interconnect delays only ever reach the manager from an earlier
// backannotation, so this one prebackannotation state is assembled directly.
// An empty SDF provides nothing, so the value must be left as it was.
TEST(SdfAnnotator, EmptySdfPreservesInterconnectDelay) {
  SpecifyManager mgr;
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
  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  EXPECT_EQ(mgr.GetInterconnectDelays()[0].rise, 7u);
  EXPECT_EQ(mgr.GetInterconnectDelays()[0].fall, 9u);
}

// C3 where the preserved value is not a single number. §30.5 lets a module path
// carry a list of transition delays, and every one of them is part of the value
// the file left alone -- preserving only the first would still corrupt the
// path. The six declared delays expand into all twelve transition slots, and
// the whole array has to come through untouched. Comparing against a snapshot
// taken before backannotation keeps this about §32.3: how the six values map
// onto twelve slots is §30.5's rule, not something restated here.
TEST(SdfAnnotator, UnmentionedMultiValuePathKeepsEveryTransitionSlot) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(
      BuildSpecifyFromSource("module t(input a, input b, output y, output z);\n"
                             "  specify\n"
                             "    (a => y) = 21;\n"
                             "    (b => z) = (1, 2, 3, 4, 5, 6);\n"
                             "  endspecify\n"
                             "endmodule\n",
                             f, mgr));
  const PathDelay kBefore = PathBetween(mgr, "b", "z");
  ASSERT_EQ(kBefore.delay_count, 6u);  // six written, all twelve slots filled
  ASSERT_NE(kBefore.delays[11], 0u);   // the expansion really did run

  auto result = AnnotateFileOnto(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH a y (7) (7))))
      )
    )
  )",
                                 mgr);

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 7u);  // the one the file did provide
  const PathDelay kAfter = PathBetween(mgr, "b", "z");
  EXPECT_EQ(kAfter.delay_count, kBefore.delay_count);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(kAfter.delays[i], kBefore.delays[i]) << "transition slot " << i;
  }
}

// C3 where the preserved value is a constraint carrying two limits rather than
// one. A $setuphold holds a setup limit and a hold limit, and a file that says
// nothing about the check has to leave both standing -- an annotator that reset
// the second limit while preserving the first would still be modifying a value
// the file never provided.
TEST(SdfAnnotator, UnmentionedSetupholdKeepsBothLimits) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(
      "module t(input a, input clk, input d, output y);\n"
      "  reg ntf;\n"
      "  specify\n"
      "    (a => y) = 21;\n"
      "    $setuphold(posedge clk, d, 12, 22, ntf);\n"
      "  endspecify\n"
      "endmodule\n",
      f, mgr));
  const TimingCheckEntry kBefore =
      CheckOfKind(mgr, TimingCheckKind::kSetuphold);
  ASSERT_EQ(kBefore.limit, 12u);
  ASSERT_EQ(kBefore.limit2, 22u);

  auto result = AnnotateFileOnto(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH a y (7) (7))))
      )
    )
  )",
                                 mgr);

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 7u);
  const TimingCheckEntry kAfter = CheckOfKind(mgr, TimingCheckKind::kSetuphold);
  EXPECT_EQ(kAfter.limit, 12u);
  EXPECT_EQ(kAfter.limit2, 22u);
}

// C3 where the preserved value did not come from a literal. §6.20.5 specparams
// can supply the delay of a module path, so the prebackannotation value reaches
// the path through a name lookup rather than a constant in the delay list --
// a different route into the same value. A file that mentions neither the path
// nor the specparam has to leave both as the source wrote them.
TEST(SdfAnnotator, PathDelayTakenFromSpecparamIsPreserved) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(
      BuildSpecifyFromSource("module t(input a, input b, output y, output z);\n"
                             "  specify\n"
                             "    specparam tRise = 13;\n"
                             "    (a => y) = tRise;\n"
                             "    (b => z) = 31;\n"
                             "  endspecify\n"
                             "endmodule\n",
                             f, mgr));
  ASSERT_EQ(mgr.GetPathDelay("a", "y"), 13u);  // resolved through the specparam

  auto result = AnnotateFileOnto(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH b z (7) (7))))
      )
    )
  )",
                                 mgr);

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(mgr.GetPathDelay("b", "z"), 7u);   // provided -> replaced
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 13u);  // not provided -> unchanged
  EXPECT_EQ(SpecparamOf(mgr, "tRise"), 13u);
}

// C3 inside the interconnect category, which the other tests only ever check
// against an empty file. Here the file provides a value for one interconnect
// delay and says nothing about a second, so the first must change and the
// second must stand -- the overwrite is what keeps the preservation assertion
// from passing on an annotator that simply does nothing.
TEST(SdfAnnotator, UnmentionedInterconnectSurvivesWhileSiblingIsAnnotated) {
  SpecifyManager mgr;
  InterconnectDelay named;
  named.src_port = "u1.q";
  named.dst_port = "u2.d";
  named.rise = 7;
  named.fall = 9;
  mgr.AddInterconnectDelay(named);

  InterconnectDelay untouched;
  untouched.src_port = "u3.q";
  untouched.dst_port = "u4.d";
  untouched.rise = 41;
  untouched.fall = 43;
  mgr.AddInterconnectDelay(untouched);

  auto result = AnnotateFileOnto(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (INTERCONNECT u1.q u2.d (2) (3))))
      )
    )
  )",
                                 mgr);

  EXPECT_TRUE(result.warnings.empty());
  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 2u);
  for (const auto& ic : mgr.GetInterconnectDelays()) {
    if (ic.src_port == "u1.q") {
      EXPECT_EQ(ic.rise, 2u);  // provided -> replaced
      EXPECT_EQ(ic.fall, 3u);
    } else {
      EXPECT_EQ(ic.rise, 41u);  // not provided -> unchanged
      EXPECT_EQ(ic.fall, 43u);
    }
  }
}

// C1 in a syntactic position the other warning tests never reach: an
// unannotatable construct sitting in a later cell rather than the first one.
// Warnings are collected across the whole file, so the second cell's DEVICE
// must warn just as a first cell's would, and the first cell's supported IOPATH
// must still be annotated alongside it.
TEST(SdfAnnotator, UnannotatableConstructInLaterCellStillWarns) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH a y (10) (20))))
      )
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u2)
        (DELAY (ABSOLUTE (DEVICE u2 (30) (40))))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));

  SpecifyManager mgr;
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("DEVICE"), std::string::npos);
  EXPECT_TRUE(mgr.HasPathDelay("a", "y"));
}

// All three rules at once on one file: the unrelated TIMINGENV section is
// ignored silently (C2), the unsupported DEVICE construct warns (C1), the
// supported IOPATH is annotated, and the declared b=>z path the file never
// mentions is preserved (C3). The exact warning count of one proves the
// silently-ignored and successfully-annotated constructs add nothing.
TEST(SdfAnnotator, SilentIgnoredWarnedAndAnnotatedAllCoexist) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(R"(
    (DELAYFILE
      (TIMINGENV
        (PATHCONSTRAINT a b (5))
      )
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (DEVICE u1 (3) (5))
            (IOPATH a y (1) (2))
          )
        )
      )
    )
  )",
                                   f, mgr);

  EXPECT_EQ(result.warnings.size(), 1u);
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 1u);
  EXPECT_EQ(mgr.GetPathDelay("b", "z"), 31u);
}

}  // namespace
