#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_sdf_design.h"
#include "fixture_simulator.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// §32.4.3 is about what an SDF LABEL section does to a *declared* specparam and
// to the expressions that read it, so how the specparam was declared and how
// those expressions were written is the whole subject. Every test below builds
// its SystemVerilog side from real source -- Design parses, elaborates and
// lowers a module, hands the module's specparam declarations to the production
// collector, and registers the specify block's path declarations through the
// production builder that keeps them. The SDF side is likewise real SDF text
// handed to ParseSdf. Nothing on either side is hand-assembled.
struct Design : SdfDesign {
  // Parses, elaborates and lowers `src`, then binds the manager to the
  // module's specparams and to its module path declarations. The design is
  // lowered but not yet run, so a test that wants to observe a procedural delay
  // reading an annotated specparam can annotate first and run afterwards.
  bool Build(const std::string& src) {
    if (!SdfDesign::Lower(src)) return false;
    const ModuleDecl& mod = Top();
    mgr.BindDesignSpecparams(CollectDeclaredSpecparams(mod), f.ctx, f.arena);
    for (auto* item : mod.items) {
      if (item->kind == ModuleItemKind::kGateInst) {
        mgr.AddPrimitiveDriversFromGate(*item, f.ctx, f.arena);
      }
    }
    AddPathsAndTimingChecks(mod);
    return true;
  }

  void Annotate(const std::string& sdf, SdfMtm mtm = SdfMtm::kTypical) {
    SdfFile file;
    ASSERT_TRUE(ParseSdf(sdf, file));
    AnnotateSdfToManager(file, mgr, mtm);
  }

  // The value the running design reads for `name`, which is where a LABEL
  // annotation has to land for anything that reads the specparam to see it.
  uint64_t DesignValue(std::string_view name) {
    Variable* var = f.ctx.FindVariable(name);
    return var == nullptr ? 0 : var->value.ToUint64();
  }

  // Whether the running design has any storage at all under `name`, which is
  // what a LABEL section naming something the design never declared must not
  // bring into being.
  bool DesignHasStorage(std::string_view name) {
    return f.ctx.FindVariable(name) != nullptr;
  }

  // The whole path delay entry, so a reevaluation can be checked across all
  // twelve transition slots and on a conditional path rather than only through
  // the single-value lookup.
  const PathDelay* Path(std::string_view src, std::string_view dst,
                        std::string_view condition = {}) {
    for (const auto& pd : mgr.GetPathDelays()) {
      if (pd.src_port == src && pd.dst_port == dst &&
          pd.condition == condition) {
        return &pd;
      }
    }
    return nullptr;
  }

  // The declared timing check of one kind, whose constraint limits are the
  // other place a specparam-bearing expression gets reduced to a number.
  const TimingCheckEntry* Check(TimingCheckKind kind) {
    for (const auto& tc : mgr.GetTimingChecks()) {
      if (tc.kind == kind) return &tc;
    }
    return nullptr;
  }

  // The registered driver of one module output, whose propagation delay is the
  // third place a specparam-bearing expression gets reduced to a number.
  const PrimitiveDriver* Driver(std::string_view output) {
    for (const auto& drv : mgr.GetPrimitiveDrivers()) {
      if (drv.output_port == output) return &drv;
    }
    return nullptr;
  }
};

// Wraps a LABEL body in the enclosing DELAYFILE/CELL structure an SDF file
// always supplies, so each test writes only the entries under test.
std::string SdfLabel(const std::string& body) {
  return "(DELAYFILE (CELL (CELLTYPE \"m\") (INSTANCE u1) (LABEL " + body +
         ")))";
}

// §32.4.3's own example: specparams control when a clock transitions, and the
// LABEL construct sets their values.
const char* const kClockSrc =
    "module clock(clk);\n"
    "  output clk;\n"
    "  reg clk;\n"
    "  specparam dhigh = 0, dlow = 0;\n"
    "  initial begin\n"
    "    clk = 0;\n"
    "    #dhigh clk = 1;\n"
    "    #dlow  clk = 0;\n"
    "    $display(\"done=%0d\", $time);\n"
    "  end\n"
    "endmodule\n";

// §32.4.3's second example: a specparam in the delay expression of a specify
// path. `cap` is declared in the specify block, the declaration site this
// implementation resolves in a path delay expression.
const char* const kPathSrc =
    "module m(input a, input b, output z, output y);\n"
    "  specify\n"
    "    specparam cap = 5;\n"
    "    (a => z) = 2 * cap + 3;\n"
    "    (b => y) = 8;\n"
    "  endspecify\n"
    "endmodule\n";

// ---------------------------------------------------------------------------
// The LABEL construct annotates to specparams.
// ---------------------------------------------------------------------------

// §32.4.3: an ABSOLUTE LABEL section carries new values for the specparams it
// names, and those values reach both the annotator's record and the storage the
// running design reads the specparam from.
TEST(SdfLabelAnnotation, AbsoluteLabelSetsDeclaredSpecparamValues) {
  Design d;
  ASSERT_TRUE(d.Build(kClockSrc));
  EXPECT_EQ(d.DesignValue("dhigh"), 0u);
  EXPECT_EQ(d.DesignValue("dlow"), 0u);

  d.Annotate(SdfLabel("(ABSOLUTE (dhigh 60) (dlow 40))"));

  const auto& vals = d.mgr.GetSpecparamValues();
  ASSERT_EQ(vals.size(), 2u);
  EXPECT_EQ(vals[0].name, "dhigh");
  EXPECT_EQ(vals[0].value, 60u);
  EXPECT_EQ(vals[1].name, "dlow");
  EXPECT_EQ(vals[1].value, 40u);

  EXPECT_EQ(d.DesignValue("dhigh"), 60u);
  EXPECT_EQ(d.DesignValue("dlow"), 40u);
}

// §32.4.3: the INCREMENT form of a LABEL section changes the same specparams,
// adding to what they already hold rather than replacing it.
TEST(SdfLabelAnnotation, IncrementLabelAddsToDeclaredSpecparamValue) {
  Design d;
  ASSERT_TRUE(d.Build(kClockSrc));

  d.Annotate(SdfLabel("(ABSOLUTE (dhigh 60))"));
  ASSERT_EQ(d.DesignValue("dhigh"), 60u);

  d.Annotate(SdfLabel("(INCREMENT (dhigh 5))"));
  EXPECT_EQ(d.DesignValue("dhigh"), 65u);
}

// §32.4.3: a LABEL value may be given as a min:typ:max triple rather than a
// single number, in which case the member the annotation run selects is the one
// that lands on the specparam.
TEST(SdfLabelAnnotation, LabelTripleValueSelectsPerDelayMode) {
  const std::string kSdf = SdfLabel("(ABSOLUTE (dhigh (10:20:30)))");

  Design min;
  ASSERT_TRUE(min.Build(kClockSrc));
  min.Annotate(kSdf, SdfMtm::kMinimum);
  EXPECT_EQ(min.DesignValue("dhigh"), 10u);

  Design typ;
  ASSERT_TRUE(typ.Build(kClockSrc));
  typ.Annotate(kSdf, SdfMtm::kTypical);
  EXPECT_EQ(typ.DesignValue("dhigh"), 20u);

  Design max;
  ASSERT_TRUE(max.Build(kClockSrc));
  max.Annotate(kSdf, SdfMtm::kMaximum);
  EXPECT_EQ(max.DesignValue("dhigh"), 30u);
}

// §32.4.3: a specparam declared among the module items and one declared inside
// a specify block are both specparams, so a LABEL section reaches either.
TEST(SdfLabelAnnotation, BothSpecparamDeclarationSitesAreAnnotatable) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m(input a, output z);\n"
              "  specparam outer = 1;\n"
              "  specify\n"
              "    specparam inner = 2;\n"
              "    (a => z) = 8;\n"
              "  endspecify\n"
              "endmodule\n"));

  const auto& declared = d.mgr.GetDeclaredSpecparams();
  ASSERT_EQ(declared.size(), 2u);
  EXPECT_EQ(declared[0], "outer");
  EXPECT_EQ(declared[1], "inner");

  d.Annotate(SdfLabel("(ABSOLUTE (outer 11) (inner 22))"));
  EXPECT_EQ(d.DesignValue("outer"), 11u);
  EXPECT_EQ(d.DesignValue("inner"), 22u);
}

// §32.4.3, the negative form: a LABEL section annotates to specparams. A name
// the module declared as something else -- here an ordinary variable -- is not
// a specparam, so the annotation leaves the design's value for it alone even
// though the annotator still records what the file asked for.
TEST(SdfLabelAnnotation, LabelDoesNotAnnotateToANameThatIsNotASpecparam) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m;\n"
              "  specparam sp = 1;\n"
              "  reg [31:0] notaspec;\n"
              "  initial notaspec = 7;\n"
              "endmodule\n"));
  d.f.scheduler.Run();
  ASSERT_EQ(d.DesignValue("notaspec"), 7u);

  d.Annotate(SdfLabel("(ABSOLUTE (notaspec 99) (sp 42))"));

  EXPECT_EQ(d.DesignValue("notaspec"), 7u);
  EXPECT_EQ(d.DesignValue("sp"), 42u);
}

// §32.4.3, the negative form: a LABEL section annotates to specparams, so a
// name the design never declared at all has nothing for it to reach. The
// annotation must not conjure up storage for that name, and the specparams the
// design does declare are left where they were.
TEST(SdfLabelAnnotation, LabelNamingAnUndeclaredSpecparamReachesNothing) {
  Design d;
  ASSERT_TRUE(d.Build(kClockSrc));

  d.Annotate(SdfLabel("(ABSOLUTE (nosuchparam 99))"));

  EXPECT_FALSE(d.DesignHasStorage("nosuchparam"));
  EXPECT_EQ(d.DesignValue("dhigh"), 0u);
  EXPECT_EQ(d.DesignValue("dlow"), 0u);
}

// §32.4.3: a specparam declared with an explicit range is still a specparam, so
// a LABEL section reaches it and the annotated value is what the design reads.
TEST(SdfLabelAnnotation, LabelReachesASpecparamDeclaredWithARange) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m;\n"
              "  specparam [7:0] byte_delay = 3;\n"
              "endmodule\n"));
  ASSERT_EQ(d.DesignValue("byte_delay"), 3u);

  d.Annotate(SdfLabel("(ABSOLUTE (byte_delay 200))"));

  EXPECT_EQ(d.DesignValue("byte_delay"), 200u);
}

// §32.4.3: a specparam's declared value is a constant expression, and the
// annotation replaces whatever that expression produced. A folded arithmetic
// literal expression reaches the specparam by a different route than a plain
// literal does, and the LABEL section overrides it just the same.
TEST(SdfLabelAnnotation,
     LabelOverridesASpecparamDeclaredFromALiteralExpression) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m;\n"
              "  specparam sp = 4 + 3;\n"
              "endmodule\n"));
  ASSERT_EQ(d.DesignValue("sp"), 7u);

  d.Annotate(SdfLabel("(ABSOLUTE (sp 55))"));

  EXPECT_EQ(d.DesignValue("sp"), 55u);
}

// §32.4.3: the same when the specparam's declared value comes from a module
// parameter rather than a literal -- it is still a specparam, so the LABEL
// section reaches it and the annotated value displaces the parameter's.
TEST(SdfLabelAnnotation, LabelOverridesASpecparamDeclaredFromAParameter) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m;\n"
              "  parameter P = 7;\n"
              "  specparam sp = P;\n"
              "endmodule\n"));
  ASSERT_EQ(d.DesignValue("sp"), 7u);

  d.Annotate(SdfLabel("(ABSOLUTE (sp 55))"));

  EXPECT_EQ(d.DesignValue("sp"), 55u);
  // The parameter itself is not a specparam, so it keeps its own value.
  EXPECT_EQ(d.DesignValue("P"), 7u);
}

// §32.4.3: and the same again for a localparam-derived declared value, which
// resolves by yet another route.
TEST(SdfLabelAnnotation, LabelOverridesASpecparamDeclaredFromALocalparam) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m;\n"
              "  localparam L = 9;\n"
              "  specparam sp = L;\n"
              "endmodule\n"));
  ASSERT_EQ(d.DesignValue("sp"), 9u);

  d.Annotate(SdfLabel("(ABSOLUTE (sp 55))"));

  EXPECT_EQ(d.DesignValue("sp"), 55u);
  EXPECT_EQ(d.DesignValue("L"), 9u);
}

// §32.4.3, the negative form on the LABEL body itself: only a section carrying
// values annotates specparams. A body that is some other kind of section names
// no new specparam values, so nothing is annotated and the design is untouched.
TEST(SdfLabelAnnotation, LabelBodyThatIsNotAValueSectionAnnotatesNothing) {
  Design d;
  ASSERT_TRUE(d.Build(kClockSrc));

  SdfFile file;
  ASSERT_TRUE(ParseSdf(SdfLabel("(SOMEOTHERSECTION (dhigh 60))"), file));
  AnnotateSdfToManager(file, d.mgr, SdfMtm::kTypical);

  EXPECT_TRUE(d.mgr.GetSpecparamValues().empty());
  EXPECT_EQ(d.DesignValue("dhigh"), 0u);
}

// §32.4.3: a LABEL section is data the annotator understands and places, so it
// is never reported as something that could not be annotated (§32.3 reserves
// that report for data with no home).
TEST(SdfLabelAnnotation, LabelDoesNotProduceUnannotatableWarning) {
  Design d;
  ASSERT_TRUE(d.Build(kPathSrc));

  SdfFile file;
  ASSERT_TRUE(ParseSdf(SdfLabel("(ABSOLUTE (cap 12))"), file));
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, d.mgr, SdfMtm::kTypical);

  EXPECT_TRUE(file.unannotatable.empty());
  for (const auto& w : result.warnings) {
    EXPECT_EQ(w.find("LABEL"), std::string::npos)
        << "a LABEL section is annotatable data: " << w;
  }
}

// §32.4.3: a LABEL section that names no specparam carries no new values, so
// nothing is annotated and no design value moves.
TEST(SdfLabelAnnotation, EmptyLabelBodyAnnotatesNothing) {
  Design d;
  ASSERT_TRUE(d.Build(kClockSrc));

  d.Annotate(SdfLabel("(ABSOLUTE)"));

  EXPECT_TRUE(d.mgr.GetSpecparamValues().empty());
  EXPECT_EQ(d.DesignValue("dhigh"), 0u);
}

// ---------------------------------------------------------------------------
// An expression containing one or more specparams is reevaluated when a value
// is annotated to it from an SDF file.
// ---------------------------------------------------------------------------

// §32.4.3's first example, end to end: the specparams control procedural delays
// that time the clock's transitions, and a LABEL section setting them changes
// when those transitions happen. Each delay expression is a bare specparam
// name, so a design run after the annotation reads the annotated values.
TEST(SdfSpecparamReevaluation, ProceduralDelayExpressionUsesAnnotatedValue) {
  Design annotated;
  ASSERT_TRUE(annotated.Build(kClockSrc));
  annotated.Annotate(SdfLabel("(ABSOLUTE (dhigh 60) (dlow 40))"));
  testing::internal::CaptureStdout();
  annotated.f.scheduler.Run();
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "done=100\n");

  // The same source with no annotation keeps the declared values, so the run
  // above is showing the annotation at work and not the declaration.
  Design plain;
  ASSERT_TRUE(plain.Build(kClockSrc));
  testing::internal::CaptureStdout();
  plain.f.scheduler.Run();
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "done=0\n");
}

// §32.4.3's second example: a specify path delay is an expression containing a
// specparam, and it was already reduced to a number when the path was declared.
// Annotating the specparam reevaluates that expression, so the path carries the
// delay the new specparam value produces -- and it does so on every annotation,
// rather than folding once against the first value that arrives.
TEST(SdfSpecparamReevaluation, PathDelayExpressionFollowsEverySuccessiveValue) {
  Design d;
  ASSERT_TRUE(d.Build(kPathSrc));
  ASSERT_EQ(d.mgr.GetPathDelay("a", "z"), 13u);  // the declared 2 * 5 + 3

  d.Annotate(SdfLabel("(ABSOLUTE (cap 0))"));
  EXPECT_EQ(d.mgr.GetPathDelay("a", "z"), 3u);

  d.Annotate(SdfLabel("(ABSOLUTE (cap 20))"));
  EXPECT_EQ(d.mgr.GetPathDelay("a", "z"), 43u);

  // The incremental form changes the specparam too, so it reevaluates as well.
  d.Annotate(SdfLabel("(INCREMENT (cap 1))"));
  EXPECT_EQ(d.mgr.GetPathDelay("a", "z"), 45u);  // 2 * 21 + 3
}

// §32.4.3: an expression containing more than one specparam is reevaluated for
// whichever of them the annotation changed, and each reevaluation reads the
// current value of the others.
TEST(SdfSpecparamReevaluation, ExpressionWithTwoSpecparamsFollowsEither) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m(input a, output z);\n"
              "  specify\n"
              "    specparam lo = 1, hi = 2;\n"
              "    (a => z) = lo + hi;\n"
              "  endspecify\n"
              "endmodule\n"));
  ASSERT_EQ(d.mgr.GetPathDelay("a", "z"), 3u);

  d.Annotate(SdfLabel("(ABSOLUTE (lo 30))"));
  EXPECT_EQ(d.mgr.GetPathDelay("a", "z"), 32u);

  d.Annotate(SdfLabel("(ABSOLUTE (hi 40))"));
  EXPECT_EQ(d.mgr.GetPathDelay("a", "z"), 70u);
}

// §32.4.3: a path may list a delay expression per transition rather than one
// for all of them. Each listed expression contains the specparam, so the
// annotation reevaluates all of them and every transition slot follows the new
// value.
TEST(SdfSpecparamReevaluation, EveryListedDelayExpressionIsReevaluated) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m(input a, output z);\n"
              "  specify\n"
              "    specparam cap = 2;\n"
              "    (a => z) = (3 * cap, 5 * cap);\n"
              "  endspecify\n"
              "endmodule\n"));
  const PathDelay* pd = d.Path("a", "z");
  ASSERT_NE(pd, nullptr);
  ASSERT_EQ(pd->delays[0], 6u);
  ASSERT_EQ(pd->delays[1], 10u);

  d.Annotate(SdfLabel("(ABSOLUTE (cap 10))"));

  pd = d.Path("a", "z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 30u);
  EXPECT_EQ(pd->delays[1], 50u);
  // A two-delay list also fills the z transitions from those two values, so the
  // reevaluation has to redistribute them rather than patch the listed slots.
  EXPECT_EQ(pd->delays[2], 30u);
  EXPECT_EQ(pd->delays[4], 50u);
}

// §32.4.3: a delay written as a min:typ:max expression is an expression
// containing the specparam in each of its three members, so an annotation
// reevaluates it and the member the delay mode selects follows the new value.
TEST(SdfSpecparamReevaluation, MinTypMaxDelayExpressionIsReevaluated) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m(input a, output z);\n"
              "  specify\n"
              "    specparam cap = 2;\n"
              "    (a => z) = cap : 2 * cap : 3 * cap;\n"
              "  endspecify\n"
              "endmodule\n"));
  ASSERT_EQ(d.mgr.GetPathDelay("a", "z"), 4u);  // typical member, 2 * 2

  d.Annotate(SdfLabel("(ABSOLUTE (cap 7))"));

  EXPECT_EQ(d.mgr.GetPathDelay("a", "z"), 14u);  // 2 * 7
}

// §32.4.3: a state-dependent path's delay is an expression like any other, so
// annotating a specparam it reads reevaluates that path -- and reevaluation has
// to find the conditional path rather than the unconditional one beside it.
TEST(SdfSpecparamReevaluation, ConditionalPathDelayExpressionIsReevaluated) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m(input a, input sel, output z);\n"
              "  specify\n"
              "    specparam cap = 1;\n"
              "    if (sel) (a => z) = 2 * cap;\n"
              "    ifnone (a => z) = 9;\n"
              "  endspecify\n"
              "endmodule\n"));
  const PathDelay* conditional = d.Path("a", "z", "sel");
  ASSERT_NE(conditional, nullptr);
  ASSERT_EQ(conditional->delays[0], 2u);

  d.Annotate(SdfLabel("(ABSOLUTE (cap 20))"));

  conditional = d.Path("a", "z", "sel");
  ASSERT_NE(conditional, nullptr);
  EXPECT_EQ(conditional->delays[0], 40u);
  // The ifnone path's delay names no specparam, so it stays where it was.
  for (const auto& pd : d.mgr.GetPathDelays()) {
    if (pd.is_ifnone) EXPECT_EQ(pd.delays[0], 9u);
  }
}

// §32.4.3: an edge-sensitive path declares its delay the same way, so a
// specparam in that delay expression is reevaluated there too -- and the
// reevaluation has to land on the edge-sensitive entry it came from.
TEST(SdfSpecparamReevaluation, EdgeSensitivePathDelayExpressionIsReevaluated) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m(input a, output z);\n"
              "  specify\n"
              "    specparam cap = 2;\n"
              "    (posedge a => (z +: a)) = 2 * cap;\n"
              "  endspecify\n"
              "endmodule\n"));
  const PathDelay* pd = d.Path("a", "z");
  ASSERT_NE(pd, nullptr);
  ASSERT_EQ(pd->edge, SpecifyEdge::kPosedge);
  ASSERT_EQ(pd->delays[0], 4u);

  d.Annotate(SdfLabel("(ABSOLUTE (cap 10))"));

  pd = d.Path("a", "z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(pd->delays[0], 20u);
}

// §32.4.3: a module path delay is not the only expression a specparam can sit
// in. A timing check states its constraint limits as expressions too, and they
// were reduced to numbers when the check was declared, so annotating a
// specparam a limit reads reevaluates that limit.
TEST(SdfSpecparamReevaluation, TimingCheckLimitExpressionIsReevaluated) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m(input dat, input clk);\n"
              "  reg ntf;\n"
              "  specify\n"
              "    specparam cap = 3;\n"
              "    $setup(dat, posedge clk, 2 * cap, ntf);\n"
              "  endspecify\n"
              "endmodule\n"));
  const TimingCheckEntry* tc = d.Check(TimingCheckKind::kSetup);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->limit, 6u);  // the declared 2 * 3

  d.Annotate(SdfLabel("(ABSOLUTE (cap 20))"));

  tc = d.Check(TimingCheckKind::kSetup);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->limit, 40u);  // 2 * 20
}

// §32.4.3: a check that states both of its limits as expressions reading the
// specparam has both reevaluated, not just the first.
TEST(SdfSpecparamReevaluation, BothTimingCheckLimitExpressionsAreReevaluated) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m(input dat, input clk);\n"
              "  reg ntf;\n"
              "  specify\n"
              "    specparam cap = 2;\n"
              "    $setuphold(posedge clk, dat, 3 * cap, 5 * cap, ntf);\n"
              "  endspecify\n"
              "endmodule\n"));
  const TimingCheckEntry* tc = d.Check(TimingCheckKind::kSetuphold);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->limit, 6u);
  ASSERT_EQ(tc->limit2, 10u);

  d.Annotate(SdfLabel("(ABSOLUTE (cap 10))"));

  tc = d.Check(TimingCheckKind::kSetuphold);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->limit, 30u);
  EXPECT_EQ(tc->limit2, 50u);
}

// §32.4.3, the negative form at the timing check position: a limit written as a
// literal contains no specparam, so a LABEL annotation must leave it where it
// is -- here at the value an earlier SDF timing check annotation put there,
// which reevaluating from the declaration would have discarded.
TEST(SdfSpecparamReevaluation, LiteralTimingCheckLimitIsNotReevaluated) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m(input dat, input clk);\n"
              "  reg ntf;\n"
              "  specify\n"
              "    specparam cap = 3;\n"
              "    $setup(dat, posedge clk, 7, ntf);\n"
              "  endspecify\n"
              "endmodule\n"));
  ASSERT_NE(d.Check(TimingCheckKind::kSetup), nullptr);
  ASSERT_EQ(d.Check(TimingCheckKind::kSetup)->limit, 7u);

  d.Annotate(
      "(DELAYFILE (CELL (CELLTYPE \"m\") (INSTANCE u1)"
      "  (TIMINGCHECK (SETUP dat (posedge clk) (44)))))");
  ASSERT_EQ(d.Check(TimingCheckKind::kSetup)->limit, 44u);

  d.Annotate(SdfLabel("(ABSOLUTE (cap 20))"));

  EXPECT_EQ(d.Check(TimingCheckKind::kSetup)->limit, 44u);
}

// §32.4.3: a gate primitive's propagation delay is a third place an expression
// gets written, and a module-level specparam is readable there. Annotating that
// specparam reevaluates the gate's delay too.
TEST(SdfSpecparamReevaluation, GatePrimitiveDelayExpressionIsReevaluated) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m(input a, input b, output z);\n"
              "  specparam cap = 2;\n"
              "  and #(3 * cap) g1(z, a, b);\n"
              "endmodule\n"));
  const PrimitiveDriver* drv = d.Driver("z");
  ASSERT_NE(drv, nullptr);
  ASSERT_EQ(drv->delays[0], 6u);  // the declared 3 * 2

  d.Annotate(SdfLabel("(ABSOLUTE (cap 10))"));

  // Still one driver for the output -- the rebuild replaces rather than adds.
  ASSERT_EQ(d.mgr.GetPrimitiveDrivers().size(), 1u);
  drv = d.Driver("z");
  ASSERT_NE(drv, nullptr);
  EXPECT_EQ(drv->delays[0], 30u);  // 3 * 10
}

// §32.4.3, the negative form at the gate position: a gate whose delay is a
// literal holds no specparam, so a LABEL annotation leaves its driver at the
// value an earlier SDF DEVICE annotation put there.
TEST(SdfSpecparamReevaluation, LiteralGatePrimitiveDelayIsNotReevaluated) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m(input a, input b, output z);\n"
              "  specparam cap = 2;\n"
              "  and #(4) g1(z, a, b);\n"
              "endmodule\n"));
  ASSERT_NE(d.Driver("z"), nullptr);
  ASSERT_EQ(d.Driver("z")->delays[0], 4u);

  d.Annotate(
      "(DELAYFILE (CELL (CELLTYPE \"m\") (INSTANCE u1)"
      "  (DELAY (ABSOLUTE (DEVICE (66) (66))))))");
  ASSERT_EQ(d.Driver("z")->delays[0], 66u);

  d.Annotate(SdfLabel("(ABSOLUTE (cap 10))"));

  EXPECT_EQ(d.Driver("z")->delays[0], 66u);
}

// §32.4.3, the negative form: only an expression containing a specparam is
// reevaluated. The b-to-y path's delay is a literal, so a LABEL annotation
// changes nothing it depends on -- and here the delay it holds came from an
// earlier IOPATH annotation, which reevaluating would have thrown away.
TEST(SdfSpecparamReevaluation, ExpressionWithoutSpecparamIsNotReevaluated) {
  Design d;
  ASSERT_TRUE(d.Build(kPathSrc));

  d.Annotate(
      "(DELAYFILE (CELL (CELLTYPE \"m\") (INSTANCE u1)"
      "  (DELAY (ABSOLUTE (IOPATH b y (55) (55))))))");
  ASSERT_EQ(d.mgr.GetPathDelay("b", "y"), 55u);

  d.Annotate(SdfLabel("(ABSOLUTE (cap 10))"));

  EXPECT_EQ(d.mgr.GetPathDelay("b", "y"), 55u);
  EXPECT_EQ(d.mgr.GetPathDelay("a", "z"), 23u);
}

// §32.4.3: reevaluation follows the specparam the annotation actually changed.
// A LABEL naming a specparam that no path delay expression reads leaves every
// path delay -- including one an earlier IOPATH annotation had set -- alone.
TEST(SdfSpecparamReevaluation, ChangingAnUnreadSpecparamReevaluatesNothing) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m(input a, output z);\n"
              "  specparam unread = 4;\n"
              "  specify\n"
              "    specparam cap = 5;\n"
              "    (a => z) = 2 * cap + 3;\n"
              "  endspecify\n"
              "endmodule\n"));

  d.Annotate(
      "(DELAYFILE (CELL (CELLTYPE \"m\") (INSTANCE u1)"
      "  (DELAY (ABSOLUTE (IOPATH a z (99) (99))))))");
  ASSERT_EQ(d.mgr.GetPathDelay("a", "z"), 99u);

  d.Annotate(SdfLabel("(ABSOLUTE (unread 77))"));
  EXPECT_EQ(d.DesignValue("unread"), 77u);
  EXPECT_EQ(d.mgr.GetPathDelay("a", "z"), 99u);

  // Annotating the specparam the expression does read reevaluates it, which is
  // what makes the check above a statement about the expression's contents.
  d.Annotate(SdfLabel("(ABSOLUTE (cap 10))"));
  EXPECT_EQ(d.mgr.GetPathDelay("a", "z"), 23u);
}

// §32.4.3: a reevaluation hook registered against a specparam runs when a LABEL
// section annotates that specparam, and stays untouched by a LABEL that names
// any other one.
TEST(SdfSpecparamReevaluation, RegisteredReevaluatorFiresOnlyForItsSpecparam) {
  Design d;
  ASSERT_TRUE(d.Build(kClockSrc));

  uint64_t observed = 0;
  int high_calls = 0;
  int low_calls = 0;
  d.mgr.RegisterSpecparamReevaluation("dhigh", [&](uint64_t v) {
    observed = v;
    ++high_calls;
  });
  d.mgr.RegisterSpecparamReevaluation("dlow", [&](uint64_t) { ++low_calls; });

  d.Annotate(SdfLabel("(ABSOLUTE (dhigh 60))"));

  EXPECT_EQ(high_calls, 1);
  EXPECT_EQ(observed, 60u);
  EXPECT_EQ(low_calls, 0);
}

}  // namespace
