#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_sdf_design.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// §32.5 is about what a *run* of SDF constructs does, so what each construct
// finds already in place when its turn comes is the whole subject. That makes
// the starting state -- the module path the design declared, the specparam its
// delay expression reads, the sources and loads its nets carry -- part of every
// test's input, so each test builds its SystemVerilog side from real source
// (parsed, elaborated and lowered, then handed to the production collectors)
// and its SDF side from real SDF text handed to ParseSdf. Nothing on either
// side is hand-assembled.
struct Design : SdfDesign {
  bool Build(const std::string& src) {
    if (!SdfDesign::Lower(src)) return false;
    const ModuleDecl& top = Top();
    mgr.BindDesignSpecparams(CollectDeclaredSpecparams(top), f.ctx, f.arena);
    mgr.BindDesignInterconnect(CollectInterconnectTopology(*cu, top));
    AddPathsAndTimingChecks(top);

    // A declared PATHPULSE$ specparam is the other way a path's pulse limits
    // can already be set when annotation starts, so it is read from the
    // declaration and applied through the production resolver.
    std::vector<PulseControlSpecparam> pulse_specs;
    for (auto* item : top.items) {
      if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
      for (auto* si : item->specify_items) {
        if (si->kind != SpecifyItemKind::kSpecparam || !si->is_pathpulse) {
          continue;
        }
        PulseControlSpecparam s;
        s.input = si->pathpulse_input;
        s.output = si->pathpulse_output;
        s.reject = EvalExpr(si->pathpulse_reject, f.ctx, f.arena).ToUint64();
        s.has_error = si->pathpulse_error != nullptr;
        if (s.has_error) {
          s.error = EvalExpr(si->pathpulse_error, f.ctx, f.arena).ToUint64();
        }
        pulse_specs.push_back(s);
      }
    }
    mgr.ResolvePulseControlSpecparams(pulse_specs);
    return true;
  }

  SdfAnnotationResult Annotate(const std::string& sdf) {
    SdfFile file;
    EXPECT_TRUE(ParseSdf(sdf, file));
    return AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
  }

  // The whole module path delay entry, so a run of constructs can be checked
  // across all twelve transition slots and across both pulse limits rather than
  // through a single-value lookup. `condition` is how the path was declared --
  // empty for a plain path, the condition text for a state-dependent one --
  // because a run of constructs can leave two paths between the same terminals
  // holding different values.
  const PathDelay* Path(std::string_view src, std::string_view dst,
                        std::string_view condition = {}) const {
    for (const auto& pd : mgr.GetPathDelays()) {
      if (pd.src_port == src && pd.dst_port == dst &&
          pd.condition == condition) {
        return &pd;
      }
    }
    return nullptr;
  }

  // The declared timing check of one kind, the other place a construct's turn
  // in the run of annotations shows up.
  const TimingCheckEntry* Check(TimingCheckKind kind) const {
    for (const auto& tc : mgr.GetTimingChecks()) {
      if (tc.kind == kind) return &tc;
    }
    return nullptr;
  }
};

// Wraps whatever sections a test writes in the DELAYFILE/CELL structure an SDF
// file always supplies, so each test writes only the constructs under test and
// the order it writes them in is the only thing that varies.
std::string SdfCellText(const std::string& sections) {
  return "(DELAYFILE (CELL (CELLTYPE \"c\") (INSTANCE u1) " + sections + "))";
}

// One ABSOLUTE DELAY section holding the run of entries a test writes.
std::string SdfDelay(const std::string& body) {
  return SdfCellText("(DELAY (ABSOLUTE " + body + "))");
}

// A module path written with a literal delay, the plainest way a specify path
// delay can already hold a value when annotation starts. 40 leaves room above
// the pulse limits the tests annotate, so nothing is clipped to the delay.
const char* const kLiteralPathSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "  endspecify\n"
    "endmodule\n";

// The same module path, but with its delay written as an expression reading a
// specparam. This is the other way a path delay's value is produced, and it is
// what lets a LABEL construct in one section change what a DELAY construct in
// another section had already annotated.
const char* const kSpecparamPathSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    specparam cap = 12;\n"
    "    (A => Z) = cap;\n"
    "  endspecify\n"
    "endmodule\n";

// A module path whose pulse limits are already set when annotation starts, by
// a module-wide PATHPULSE$ declared in the specify block rather than by an SDF
// construct. This is the other way the "current" limits an empty-parenthesis
// IOPATH holds can have been produced.
const char* const kModulePathpulseSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "    specparam PATHPULSE$ = (21, 34);\n"
    "  endspecify\n"
    "endmodule\n";

// The path-specific spelling of the same declaration, which reaches the path by
// naming its two terminals instead of covering every path in the module.
const char* const kPathSpecificPathpulseSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "    specparam PATHPULSE$A$Z = (21, 34);\n"
    "  endspecify\n"
    "endmodule\n";

// One plain module path and one state-dependent path between the same two
// terminals, so a later construct can be narrower than the earlier one and
// change only part of what the earlier one reached.
const char* const kConditionalPathSrc =
    "module c(input A, input mode, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "    if (mode) (A => Z) = 50;\n"
    "  endspecify\n"
    "endmodule\n";

// A timing check whose constraint limit is written as an expression reading a
// specparam. It is the other kind of value a LABEL construct reaches, so it is
// what lets a TIMINGCHECK section and a LABEL section be put in either order.
const char* const kSpecparamCheckSrc =
    "module c(input D, input CK);\n"
    "  specify\n"
    "    specparam lim = 5;\n"
    "    $setup(posedge CK, D, lim);\n"
    "  endspecify\n"
    "endmodule\n";

// §32.5's own multiple-annotation example: a net with three sources and a
// single load, so a PORT construct naming only the load and an INTERCONNECT
// construct naming one of the three sources both have somewhere to land.
const char* const kThreeSourceSrc =
    "module drv(out);\n"
    "  output out;\n"
    "  reg out;\n"
    "endmodule\n"
    "module ld(in);\n"
    "  input in;\n"
    "  wire in;\n"
    "endmodule\n"
    "module top;\n"
    "  wire n;\n"
    "  drv i13(.out(n));\n"
    "  drv i11(.out(n));\n"
    "  drv i12(.out(n));\n"
    "  ld i15(.in(n));\n"
    "endmodule\n";

// Two sources on one net that transition at different times, so each source's
// own arrival at the shared load can be told apart at run time.
const char* const kStaggeredSourceSrc =
    "module drv_a(out);\n"
    "  output out;\n"
    "  reg out;\n"
    "  initial begin out = 1'b0; #5 out = 1'b1; end\n"
    "endmodule\n"
    "module drv_b(out);\n"
    "  output out;\n"
    "  reg out;\n"
    "  initial begin out = 1'b0; #20 out = 1'b1; end\n"
    "endmodule\n"
    "module ld(in);\n"
    "  input in;\n"
    "  wire in;\n"
    "endmodule\n"
    "module top;\n"
    "  wire n;\n"
    "  drv_a i13(.out(n));\n"
    "  drv_b i11(.out(n));\n"
    "  ld i15(.in(n));\n"
    "endmodule\n";

// Two loads on one net, so a construct aimed at one load can be shown to leave
// what was annotated to the other load alone.
const char* const kTwoLoadSrc =
    "module drv(out);\n"
    "  output out;\n"
    "  reg out;\n"
    "endmodule\n"
    "module ld(in);\n"
    "  input in;\n"
    "  wire in;\n"
    "endmodule\n"
    "module top;\n"
    "  wire n;\n"
    "  drv i13(.out(n));\n"
    "  ld i14(.in(n));\n"
    "  ld i15(.in(n));\n"
    "endmodule\n";

// ---------------------------------------------------------------------------
// Annotation is an ordered process: constructs are applied in the order the
// file writes them.
// ---------------------------------------------------------------------------

// §32.5's own example of the ordering: pulse limits are annotated to a path
// first, then the whole path is annotated, which overwrites the limits that
// were just put there. The two constructs are of different kinds, which is
// exactly the point -- a construct's annotation can be undone by a later one
// that is not the same construct.
TEST(SdfMultipleAnnotations, PathpulseThenIopathLosesTheAnnotatedPulseLimits) {
  Design d;
  ASSERT_TRUE(d.Build(kLiteralPathSrc));

  d.Annotate(SdfDelay("(PATHPULSE A Z (21) (34)) (IOPATH A Z (35) (61))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 35u);
  EXPECT_EQ(pd->delays[1], 61u);
  // Nothing of the PATHPULSE survives: each limit is back to what the IOPATH's
  // own delay produces.
  EXPECT_EQ(pd->reject_limit[0], 35u);
  EXPECT_EQ(pd->error_limit[0], 35u);
  EXPECT_EQ(pd->reject_limit[1], 61u);
  EXPECT_EQ(pd->error_limit[1], 61u);
}

// The same two constructs the other way round produce the opposite result,
// which is what makes the process an ordered one rather than a set of
// independent updates.
TEST(SdfMultipleAnnotations, IopathThenPathpulseKeepsTheAnnotatedPulseLimits) {
  Design d;
  ASSERT_TRUE(d.Build(kLiteralPathSrc));

  d.Annotate(SdfDelay("(IOPATH A Z (35) (61)) (PATHPULSE A Z (21) (34))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 35u);
  EXPECT_EQ(pd->delays[1], 61u);
  EXPECT_EQ(pd->reject_limit[0], 21u);
  EXPECT_EQ(pd->error_limit[0], 34u);
}

// Two constructs of the same kind on the same path: the later one is what the
// path is left holding.
TEST(SdfMultipleAnnotations, LaterIopathReplacesTheEarlierOneOnTheSamePath) {
  Design d;
  ASSERT_TRUE(d.Build(kLiteralPathSrc));

  d.Annotate(SdfDelay("(IOPATH A Z (35) (61)) (IOPATH A Z (7) (9))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 7u);
  EXPECT_EQ(pd->delays[1], 9u);
}

// The ordering runs across the cell's sections, not merely within one of them.
// A LABEL construct reprices a specparam, and reevaluating the path delay
// expression that reads it undoes the IOPATH written before it.
TEST(SdfMultipleAnnotations, LabelAfterIopathOverwritesTheAnnotatedPathDelay) {
  Design d;
  ASSERT_TRUE(d.Build(kSpecparamPathSrc));
  ASSERT_NE(d.Path("A", "Z"), nullptr);
  ASSERT_EQ(d.Path("A", "Z")->delays[0], 12u);

  d.Annotate(SdfCellText(
      "(DELAY (ABSOLUTE (IOPATH A Z (7)))) (LABEL (ABSOLUTE (cap 30)))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 30u);
}

// The same two sections the other way round: the IOPATH now runs last, so the
// path is left holding the IOPATH's delay even though the specparam its
// declared expression reads was annotated to something else.
TEST(SdfMultipleAnnotations, IopathAfterLabelOverwritesTheReevaluatedDelay) {
  Design d;
  ASSERT_TRUE(d.Build(kSpecparamPathSrc));

  d.Annotate(SdfCellText(
      "(LABEL (ABSOLUTE (cap 30))) (DELAY (ABSOLUTE (IOPATH A Z (7))))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 7u);
  // The LABEL still did its own job -- only its effect on this path was
  // overwritten by the construct written after it.
  EXPECT_EQ(d.f.ctx.FindVariable("cap")->value.ToUint64(), 30u);
}

// The ordering reaches a TIMINGCHECK section too: a LABEL written after one
// reprices the specparam the declared constraint limit reads, and reevaluating
// it undoes the limit the TIMINGCHECK had just annotated.
TEST(SdfMultipleAnnotations, LabelAfterTimingcheckOverwritesTheAnnotatedLimit) {
  Design d;
  ASSERT_TRUE(d.Build(kSpecparamCheckSrc));
  ASSERT_NE(d.Check(TimingCheckKind::kSetup), nullptr);
  ASSERT_EQ(d.Check(TimingCheckKind::kSetup)->limit, 5u);

  d.Annotate(
      SdfCellText("(TIMINGCHECK (SETUP D (posedge CK) (20)))"
                  " (LABEL (ABSOLUTE (lim 40)))"));

  EXPECT_EQ(d.Check(TimingCheckKind::kSetup)->limit, 40u);
}

// The same two sections the other way round, so the TIMINGCHECK now runs last
// and its constraint value is what the check is left holding.
TEST(SdfMultipleAnnotations, TimingcheckAfterLabelUndoesTheReevaluation) {
  Design d;
  ASSERT_TRUE(d.Build(kSpecparamCheckSrc));

  d.Annotate(
      SdfCellText("(LABEL (ABSOLUTE (lim 40)))"
                  " (TIMINGCHECK (SETUP D (posedge CK) (20)))"));

  EXPECT_EQ(d.Check(TimingCheckKind::kSetup)->limit, 20u);
}

// A later construct may be narrower than an earlier one, in which case only the
// part it reaches is changed and the rest keeps the earlier annotation. A plain
// IOPATH reaches both paths between the two terminals; the conditioned one
// after it reaches only the path declared under that condition.
TEST(SdfMultipleAnnotations, NarrowerLaterIopathChangesOnlyThePathItNames) {
  Design d;
  ASSERT_TRUE(d.Build(kConditionalPathSrc));

  d.Annotate(SdfDelay("(IOPATH A Z (35)) (COND mode (IOPATH A Z (7)))"));

  const auto* plain = d.Path("A", "Z");
  const auto* conditional = d.Path("A", "Z", "mode");
  ASSERT_NE(plain, nullptr);
  ASSERT_NE(conditional, nullptr);
  EXPECT_EQ(plain->delays[0], 35u);
  EXPECT_EQ(conditional->delays[0], 7u);
}

// A construct the annotator cannot take in drops out of the run without
// disturbing it: the entries written on either side of it still apply in the
// order they were written, and the one that could not be placed is reported.
TEST(SdfMultipleAnnotations, UnannotatableEntryDoesNotDisturbTheRun) {
  Design d;
  ASSERT_TRUE(d.Build(kLiteralPathSrc));

  const auto result = d.Annotate(
      SdfDelay("(IOPATH A Z (35)) (NOSUCHENTRY A Z (99)) (IOPATH A Z (7))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 7u);

  bool warned = false;
  for (const auto& w : result.warnings) {
    if (w.find("NOSUCHENTRY") != std::string::npos) warned = true;
  }
  EXPECT_TRUE(warned);
}

// The ordering spans the whole file, not one cell of it. Two cells naming the
// same instance are one run of constructs, so the later cell's entry is what
// the path is left holding.
TEST(SdfMultipleAnnotations, LaterCellInTheSameFileOverwritesTheEarlierOne) {
  Design d;
  ASSERT_TRUE(d.Build(kLiteralPathSrc));

  d.Annotate(
      "(DELAYFILE"
      " (CELL (CELLTYPE \"c\") (INSTANCE u1)"
      "  (DELAY (ABSOLUTE (IOPATH A Z (35) (61)))))"
      " (CELL (CELLTYPE \"c\") (INSTANCE u1)"
      "  (DELAY (ABSOLUTE (IOPATH A Z (7) (9))))))");

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 7u);
  EXPECT_EQ(pd->delays[1], 9u);
}

// ---------------------------------------------------------------------------
// A later construct either overwrites (ABSOLUTE) or modifies (INCREMENT) what
// an earlier one annotated.
// ---------------------------------------------------------------------------

// The modifying half: an INCREMENT section adds to the value standing after the
// ABSOLUTE section rather than replacing it.
TEST(SdfMultipleAnnotations, IncrementSectionModifiesTheEarlierAnnotation) {
  Design d;
  ASSERT_TRUE(d.Build(kLiteralPathSrc));

  d.Annotate(
      SdfCellText("(DELAY (ABSOLUTE (IOPATH A Z (35) (61))))"
                  " (DELAY (INCREMENT (IOPATH A Z (5) (5))))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 40u);
  EXPECT_EQ(pd->delays[1], 66u);
}

// The overwriting half, and the negative form of the test above: an ABSOLUTE
// section written after an INCREMENT section discards what the INCREMENT
// accumulated instead of adding to it.
TEST(SdfMultipleAnnotations, AbsoluteSectionOverwritesTheEarlierIncrement) {
  Design d;
  ASSERT_TRUE(d.Build(kLiteralPathSrc));

  d.Annotate(
      SdfCellText("(DELAY (INCREMENT (IOPATH A Z (5) (5))))"
                  " (DELAY (ABSOLUTE (IOPATH A Z (35) (61))))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 35u);
  EXPECT_EQ(pd->delays[1], 61u);
}

// Modifying rather than overwriting applies to the interconnect constructs as
// well: an INCREMENT INTERCONNECT adds to the delay the ABSOLUTE one annotated
// to the same source and load.
TEST(SdfMultipleAnnotations, IncrementInterconnectModifiesTheEarlierOne) {
  Design d;
  ASSERT_TRUE(d.Build(kThreeSourceSrc));

  d.Annotate(
      SdfCellText("(DELAY (ABSOLUTE (INTERCONNECT i13/out i15/in (5))))"
                  " (DELAY (INCREMENT (INTERCONNECT i13/out i15/in (4))))"));

  const auto* got = d.mgr.FindInterconnectDelay("i13/out", "i15/in");
  ASSERT_NE(got, nullptr);
  EXPECT_EQ(got->delays[0], 9u);
}

// An increment modifies whatever delay is in force, which for a source with no
// entry of its own is the one the PORT construct before it annotated. So the
// named source ends up at the PORT delay plus the increment, and the sources
// the increment did not name stay at the PORT delay.
TEST(SdfMultipleAnnotations, IncrementInterconnectAddsToThePortDelay) {
  Design d;
  ASSERT_TRUE(d.Build(kThreeSourceSrc));

  d.Annotate(
      SdfCellText("(DELAY (ABSOLUTE (PORT i15/in (6))))"
                  " (DELAY (INCREMENT (INTERCONNECT i13/out i15/in (4))))"));

  const auto* from_named = d.mgr.FindInterconnectDelay("i13/out", "i15/in");
  const auto* from_other = d.mgr.FindInterconnectDelay("i11/out", "i15/in");
  ASSERT_NE(from_named, nullptr);
  ASSERT_NE(from_other, nullptr);
  EXPECT_EQ(from_named->delays[0], 10u);
  EXPECT_EQ(from_other->delays[0], 6u);
}

// The same rule the other way round: an increment carrying no source of its own
// raises the delay from every source, so it reaches the entry a preceding
// INTERCONNECT construct left for its own source as well as the rest.
TEST(SdfMultipleAnnotations, IncrementPortAddsToEverySourceOnTheLoad) {
  Design d;
  ASSERT_TRUE(d.Build(kThreeSourceSrc));

  d.Annotate(
      SdfCellText("(DELAY (ABSOLUTE (INTERCONNECT i13/out i15/in (5))))"
                  " (DELAY (INCREMENT (PORT i15/in (4))))"));

  const auto* from_named = d.mgr.FindInterconnectDelay("i13/out", "i15/in");
  const auto* from_other = d.mgr.FindInterconnectDelay("i11/out", "i15/in");
  ASSERT_NE(from_named, nullptr);
  ASSERT_NE(from_other, nullptr);
  EXPECT_EQ(from_named->delays[0], 9u);
  EXPECT_EQ(from_other->delays[0], 4u);
}

// The modifying half on the LABEL construct: an INCREMENT LABEL adds to the
// specparam value the ABSOLUTE LABEL before it annotated, and the path delay
// expression that reads the specparam follows the accumulated value.
TEST(SdfMultipleAnnotations, IncrementLabelModifiesTheEarlierLabel) {
  Design d;
  ASSERT_TRUE(d.Build(kSpecparamPathSrc));

  d.Annotate(
      SdfCellText("(LABEL (ABSOLUTE (cap 30))) (LABEL (INCREMENT (cap 5)))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 35u);
}

// ---------------------------------------------------------------------------
// Holding the current pulse limits with empty parentheses.
// ---------------------------------------------------------------------------

// §32.5's remedy for the first example above: writing the IOPATH's pulse limits
// as empty parentheses holds whatever the earlier PATHPULSE annotated instead
// of overwriting it, while the delays it does carry still take effect.
TEST(SdfMultipleAnnotations, EmptyPulseParenthesesHoldTheCurrentPulseLimits) {
  Design d;
  ASSERT_TRUE(d.Build(kLiteralPathSrc));

  d.Annotate(
      SdfDelay("(PATHPULSE A Z (21) (34))"
               " (IOPATH A Z ((35) () ()) ((61) () ()))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 35u);
  EXPECT_EQ(pd->delays[1], 61u);
  EXPECT_EQ(pd->reject_limit[0], 21u);
  EXPECT_EQ(pd->error_limit[0], 34u);
  EXPECT_EQ(pd->reject_limit[1], 21u);
  EXPECT_EQ(pd->error_limit[1], 34u);
}

// Each of the two limits is held or overwritten on its own. Here the reject
// limit is written as a value and the error limit as empty parentheses, so only
// the error limit keeps what the PATHPULSE annotated.
TEST(SdfMultipleAnnotations, EmptyErrorParenthesesHoldOnlyTheErrorLimit) {
  Design d;
  ASSERT_TRUE(d.Build(kLiteralPathSrc));

  d.Annotate(
      SdfDelay("(PATHPULSE A Z (21) (34))"
               " (IOPATH A Z ((35) (8) ()) ((61) (8) ()))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 35u);
  EXPECT_EQ(pd->reject_limit[0], 8u);
  EXPECT_EQ(pd->error_limit[0], 34u);
}

// The other way round: the reject limit is left empty and the error limit given
// a value, so this time it is the reject limit that survives from before.
TEST(SdfMultipleAnnotations, EmptyRejectParenthesesHoldOnlyTheRejectLimit) {
  Design d;
  ASSERT_TRUE(d.Build(kLiteralPathSrc));

  d.Annotate(
      SdfDelay("(PATHPULSE A Z (21) (34))"
               " (IOPATH A Z ((35) () (30)) ((61) () (30)))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 35u);
  EXPECT_EQ(pd->reject_limit[0], 21u);
  EXPECT_EQ(pd->error_limit[0], 30u);
}

// What is being held need not have come from an SDF construct at all. Here the
// limits standing when annotation starts were set by a module-wide PATHPULSE$
// declared in the specify block, and the empty parentheses hold those.
TEST(SdfMultipleAnnotations, EmptyParenthesesHoldDeclaredModulePulseLimits) {
  Design d;
  ASSERT_TRUE(d.Build(kModulePathpulseSrc));
  ASSERT_NE(d.Path("A", "Z"), nullptr);
  ASSERT_EQ(d.Path("A", "Z")->reject_limit[0], 21u);

  d.Annotate(SdfDelay("(IOPATH A Z ((35) () ()) ((61) () ()))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 35u);
  EXPECT_EQ(pd->reject_limit[0], 21u);
  EXPECT_EQ(pd->error_limit[0], 34u);
}

// The negative form for that same starting state: with the limits written as
// values rather than left empty, nothing of the declared PATHPULSE$ survives.
TEST(SdfMultipleAnnotations, PlainIopathDiscardsDeclaredModulePulseLimits) {
  Design d;
  ASSERT_TRUE(d.Build(kModulePathpulseSrc));

  d.Annotate(SdfDelay("(IOPATH A Z (35) (61))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 35u);
  EXPECT_EQ(pd->error_limit[0], 35u);
}

// The path-specific spelling of the declaration reaches the path a different
// way, and the limits it leaves behind are held just the same.
TEST(SdfMultipleAnnotations, EmptyParenthesesHoldDeclaredPathPulseLimits) {
  Design d;
  ASSERT_TRUE(d.Build(kPathSpecificPathpulseSrc));
  ASSERT_NE(d.Path("A", "Z"), nullptr);
  ASSERT_EQ(d.Path("A", "Z")->error_limit[0], 34u);

  d.Annotate(SdfDelay("(IOPATH A Z ((35) () ()) ((61) () ()))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 35u);
  EXPECT_EQ(pd->reject_limit[0], 21u);
  EXPECT_EQ(pd->error_limit[0], 34u);
}

// The pair of constructs above can be written as the single equivalent
// statement that spells the held limits out, and the two forms shall leave the
// path in the same state -- across every transition slot, not only the first.
TEST(SdfMultipleAnnotations, CombinedIopathMatchesPathpulseThenHeldIopath) {
  Design separate;
  ASSERT_TRUE(separate.Build(kLiteralPathSrc));
  separate.Annotate(
      SdfDelay("(PATHPULSE A Z (21) (34))"
               " (IOPATH A Z ((35) () ()) ((61) () ()))"));

  Design combined;
  ASSERT_TRUE(combined.Build(kLiteralPathSrc));
  combined.Annotate(SdfDelay("(IOPATH A Z ((35) (21) (34)) ((61) (21) (34)))"));

  const auto* lhs = separate.Path("A", "Z");
  const auto* rhs = combined.Path("A", "Z");
  ASSERT_NE(lhs, nullptr);
  ASSERT_NE(rhs, nullptr);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(rhs->delays[i], lhs->delays[i]) << "delay slot " << i;
    EXPECT_EQ(rhs->reject_limit[i], lhs->reject_limit[i])
        << "reject slot " << i;
    EXPECT_EQ(rhs->error_limit[i], lhs->error_limit[i]) << "error slot " << i;
  }
}

// ---------------------------------------------------------------------------
// PORT followed by INTERCONNECT: only the delay from the named source changes.
// ---------------------------------------------------------------------------

// §32.5's own example: on a net with three sources and one load, a PORT
// construct gives the load one delay from every source, and an INTERCONNECT
// construct written after it changes only the delay from the source it names.
// The other two sources keep the delay the PORT construct annotated.
TEST(SdfMultipleAnnotations, InterconnectAfterPortChangesOnlyItsOwnSource) {
  Design d;
  ASSERT_TRUE(d.Build(kThreeSourceSrc));

  d.Annotate(SdfDelay("(PORT i15/in (6)) (INTERCONNECT i13/out i15/in (5))"));

  const auto* from_named = d.mgr.FindInterconnectDelay("i13/out", "i15/in");
  const auto* from_other1 = d.mgr.FindInterconnectDelay("i11/out", "i15/in");
  const auto* from_other2 = d.mgr.FindInterconnectDelay("i12/out", "i15/in");
  ASSERT_NE(from_named, nullptr);
  ASSERT_NE(from_other1, nullptr);
  ASSERT_NE(from_other2, nullptr);
  EXPECT_EQ(from_named->delays[0], 5u);
  EXPECT_EQ(from_other1->delays[0], 6u);
  EXPECT_EQ(from_other2->delays[0], 6u);
}

// Running the design: each source's own transition reaches the shared load
// after the delay that source is annotated with, so the pair of annotations is
// visible in the arrivals and not only in the recorded values.
TEST(SdfMultipleAnnotations, EachSourceArrivesWithItsOwnDelayAtRuntime) {
  Design d;
  ASSERT_TRUE(d.Build(kStaggeredSourceSrc));
  d.Annotate(SdfDelay("(PORT i15/in (6)) (INTERCONNECT i13/out i15/in (5))"));

  d.mgr.StartInterconnectPropagation(d.f.ctx, d.f.scheduler);
  d.f.scheduler.Run();

  // The named source rises at 5 and so arrives at 10 carrying the
  // INTERCONNECT's delay; the other source rises at 20 and so arrives at 26
  // still carrying the PORT's delay.
  bool named_arrived = false;
  bool other_arrived = false;
  for (const auto& a : d.mgr.GetInterconnectArrivals()) {
    if (a.load_port != "i15/in") continue;
    if (a.time == 10 && a.delay == 5) named_arrived = true;
    if (a.time == 26 && a.delay == 6) other_arrived = true;
  }
  EXPECT_TRUE(named_arrived) << "no arrival carrying the INTERCONNECT delay";
  EXPECT_TRUE(other_arrived) << "no arrival carrying the PORT delay";
}

// ---------------------------------------------------------------------------
// INTERCONNECT followed by PORT: the interconnect annotation is overwritten.
// ---------------------------------------------------------------------------

// §32.5's second example: with the two constructs the other way round, the
// PORT construct overwrites the INTERCONNECT annotation, so the delay from
// every source to that load -- the one the INTERCONNECT named included --
// becomes the PORT's delay.
TEST(SdfMultipleAnnotations, PortAfterInterconnectOverwritesItForEverySource) {
  Design d;
  ASSERT_TRUE(d.Build(kThreeSourceSrc));

  d.Annotate(SdfDelay("(INTERCONNECT i13/out i15/in (5)) (PORT i15/in (6))"));

  for (const char* source : {"i13/out", "i11/out", "i12/out"}) {
    const auto* got = d.mgr.FindInterconnectDelay(source, "i15/in");
    ASSERT_NE(got, nullptr) << source;
    EXPECT_EQ(got->delays[0], 6u) << source;
  }
}

// Running the design after the overwrite: the source the INTERCONNECT had named
// no longer has a delay of its own, so its transition reaches the load carrying
// the PORT's delay like every other source.
TEST(SdfMultipleAnnotations, OverwrittenSourceArrivesWithThePortDelay) {
  Design d;
  ASSERT_TRUE(d.Build(kStaggeredSourceSrc));
  d.Annotate(SdfDelay("(INTERCONNECT i13/out i15/in (5)) (PORT i15/in (6))"));

  d.mgr.StartInterconnectPropagation(d.f.ctx, d.f.scheduler);
  d.f.scheduler.Run();

  // The named source rises at 5, so under the INTERCONNECT's overwritten delay
  // of 5 it would have arrived at 10; under the PORT's delay it arrives at 11.
  bool arrived_with_port_delay = false;
  for (const auto& a : d.mgr.GetInterconnectArrivals()) {
    if (a.load_port != "i15/in") continue;
    EXPECT_NE(a.delay, 5u) << "a source still carries the overwritten delay";
    if (a.time == 11 && a.delay == 6) arrived_with_port_delay = true;
  }
  EXPECT_TRUE(arrived_with_port_delay);
}

// The rule is about a PORT construct and an INTERCONNECT construct reaching the
// same load. A PORT construct naming a different load overwrites nothing.
TEST(SdfMultipleAnnotations, PortOverwritesOnlyTheLoadItNames) {
  Design d;
  ASSERT_TRUE(d.Build(kTwoLoadSrc));

  d.Annotate(SdfDelay("(INTERCONNECT i13/out i14/in (5)) (PORT i15/in (6))"));

  const auto* untouched = d.mgr.FindInterconnectDelay("i13/out", "i14/in");
  ASSERT_NE(untouched, nullptr);
  EXPECT_EQ(untouched->delays[0], 5u);

  const auto* annotated = d.mgr.FindInterconnectDelay("i13/out", "i15/in");
  ASSERT_NE(annotated, nullptr);
  EXPECT_EQ(annotated->delays[0], 6u);
}

// A run of three: the PORT construct in the middle wipes the first
// INTERCONNECT, and the INTERCONNECT after it takes its own source back off the
// PORT's baseline again.
TEST(SdfMultipleAnnotations, PortBetweenInterconnectsResetsThenIsOverridden) {
  Design d;
  ASSERT_TRUE(d.Build(kThreeSourceSrc));

  d.Annotate(
      SdfDelay("(INTERCONNECT i13/out i15/in (5))"
               " (PORT i15/in (6))"
               " (INTERCONNECT i13/out i15/in (9))"));

  const auto* from_named = d.mgr.FindInterconnectDelay("i13/out", "i15/in");
  const auto* from_other = d.mgr.FindInterconnectDelay("i11/out", "i15/in");
  ASSERT_NE(from_named, nullptr);
  ASSERT_NE(from_other, nullptr);
  EXPECT_EQ(from_named->delays[0], 9u);
  EXPECT_EQ(from_other->delays[0], 6u);
}

}  // namespace
