#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_sdf_design.h"
#include "fixture_simulator.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_timing_check.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

struct Design : SdfDesign {
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

  uint64_t DesignValue(std::string_view name) {
    Variable* var = f.ctx.FindVariable(name);
    return var == nullptr ? 0 : var->value.ToUint64();
  }

  bool DesignHasStorage(std::string_view name) {
    return f.ctx.FindVariable(name) != nullptr;
  }

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

  const TimingCheckEntry* Check(TimingCheckKind kind) {
    for (const auto& tc : mgr.GetTimingChecks()) {
      if (tc.kind == kind) return &tc;
    }
    return nullptr;
  }

  const PrimitiveDriver* Driver(std::string_view output) {
    for (const auto& drv : mgr.GetPrimitiveDrivers()) {
      if (drv.output_port == output) return &drv;
    }
    return nullptr;
  }
};

std::string SdfLabel(const std::string& body) {
  return "(DELAYFILE (CELL (CELLTYPE \"m\") (INSTANCE u1) (LABEL " + body +
         ")))";
}

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

const char* const kPathSrc =
    "module m(input a, input b, output z, output y);\n"
    "  specify\n"
    "    specparam cap = 5;\n"
    "    (a => z) = 2 * cap + 3;\n"
    "    (b => y) = 8;\n"
    "  endspecify\n"
    "endmodule\n";

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

TEST(SdfLabelAnnotation, IncrementLabelAddsToDeclaredSpecparamValue) {
  Design d;
  ASSERT_TRUE(d.Build(kClockSrc));

  d.Annotate(SdfLabel("(ABSOLUTE (dhigh 60))"));
  ASSERT_EQ(d.DesignValue("dhigh"), 60u);

  d.Annotate(SdfLabel("(INCREMENT (dhigh 5))"));
  EXPECT_EQ(d.DesignValue("dhigh"), 65u);
}

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

TEST(SdfLabelAnnotation, LabelNamingAnUndeclaredSpecparamReachesNothing) {
  Design d;
  ASSERT_TRUE(d.Build(kClockSrc));

  d.Annotate(SdfLabel("(ABSOLUTE (nosuchparam 99))"));

  EXPECT_FALSE(d.DesignHasStorage("nosuchparam"));
  EXPECT_EQ(d.DesignValue("dhigh"), 0u);
  EXPECT_EQ(d.DesignValue("dlow"), 0u);
}

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
  EXPECT_EQ(d.DesignValue("P"), 7u);
}

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

TEST(SdfLabelAnnotation, LabelNamingAParameterOrLocalparamChangesNothing) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m;\n"
              "  parameter P = 7;\n"
              "  localparam L = 9;\n"
              "  specparam sp = P + L;\n"
              "endmodule\n"));
  ASSERT_EQ(d.DesignValue("sp"), 16u);

  d.Annotate(SdfLabel("(ABSOLUTE (P 42) (L 43))"));

  EXPECT_EQ(d.DesignValue("P"), 7u);
  EXPECT_EQ(d.DesignValue("L"), 9u);
  EXPECT_EQ(d.DesignValue("sp"), 16u);
}

TEST(SdfLabelAnnotation, LabelBodyThatIsNotAValueSectionAnnotatesNothing) {
  Design d;
  ASSERT_TRUE(d.Build(kClockSrc));

  SdfFile file;
  ASSERT_TRUE(ParseSdf(SdfLabel("(SOMEOTHERSECTION (dhigh 60))"), file));
  AnnotateSdfToManager(file, d.mgr, SdfMtm::kTypical);

  EXPECT_TRUE(d.mgr.GetSpecparamValues().empty());
  EXPECT_EQ(d.DesignValue("dhigh"), 0u);
}

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

TEST(SdfLabelAnnotation, EmptyLabelBodyAnnotatesNothing) {
  Design d;
  ASSERT_TRUE(d.Build(kClockSrc));

  d.Annotate(SdfLabel("(ABSOLUTE)"));

  EXPECT_TRUE(d.mgr.GetSpecparamValues().empty());
  EXPECT_EQ(d.DesignValue("dhigh"), 0u);
}

TEST(SdfSpecparamReevaluation, ProceduralDelayExpressionUsesAnnotatedValue) {
  Design annotated;
  ASSERT_TRUE(annotated.Build(kClockSrc));
  annotated.Annotate(SdfLabel("(ABSOLUTE (dhigh 60) (dlow 40))"));
  testing::internal::CaptureStdout();
  annotated.f.scheduler.Run();
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "done=100\n");

  Design plain;
  ASSERT_TRUE(plain.Build(kClockSrc));
  testing::internal::CaptureStdout();
  plain.f.scheduler.Run();
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "done=0\n");
}

TEST(SdfSpecparamReevaluation, PathDelayExpressionFollowsEverySuccessiveValue) {
  Design d;
  ASSERT_TRUE(d.Build(kPathSrc));
  ASSERT_EQ(d.mgr.GetPathDelay("a", "z"), 13u);

  d.Annotate(SdfLabel("(ABSOLUTE (cap 0))"));
  EXPECT_EQ(d.mgr.GetPathDelay("a", "z"), 3u);

  d.Annotate(SdfLabel("(ABSOLUTE (cap 20))"));
  EXPECT_EQ(d.mgr.GetPathDelay("a", "z"), 43u);

  d.Annotate(SdfLabel("(INCREMENT (cap 1))"));
  EXPECT_EQ(d.mgr.GetPathDelay("a", "z"), 45u);
}

TEST(SdfSpecparamReevaluation, FirstIncrementAddsToTheDeclaredValue) {
  Design d;
  ASSERT_TRUE(d.Build(kPathSrc));
  ASSERT_EQ(d.mgr.GetPathDelay("a", "z"), 13u);

  d.Annotate(SdfLabel("(INCREMENT (cap 1))"));
  EXPECT_EQ(d.mgr.GetPathDelay("a", "z"), 15u);
}

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
  EXPECT_EQ(pd->delays[2], 30u);
  EXPECT_EQ(pd->delays[4], 50u);
}

TEST(SdfSpecparamReevaluation, MinTypMaxDelayExpressionIsReevaluated) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m(input a, output z);\n"
              "  specify\n"
              "    specparam cap = 2;\n"
              "    (a => z) = cap : 2 * cap : 3 * cap;\n"
              "  endspecify\n"
              "endmodule\n"));
  ASSERT_EQ(d.mgr.GetPathDelay("a", "z"), 4u);

  d.Annotate(SdfLabel("(ABSOLUTE (cap 7))"));

  EXPECT_EQ(d.mgr.GetPathDelay("a", "z"), 14u);
}

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
  for (const auto& pd : d.mgr.GetPathDelays()) {
    if (pd.is_ifnone) EXPECT_EQ(pd.delays[0], 9u);
  }
}

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
  ASSERT_EQ(tc->limit, 6u);

  d.Annotate(SdfLabel("(ABSOLUTE (cap 20))"));

  tc = d.Check(TimingCheckKind::kSetup);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->limit, 40u);
}

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

TEST(SdfSpecparamReevaluation, GatePrimitiveDelayExpressionIsReevaluated) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m(input a, input b, output z);\n"
              "  specparam cap = 2;\n"
              "  and #(3 * cap) g1(z, a, b);\n"
              "endmodule\n"));
  const PrimitiveDriver* drv = d.Driver("z");
  ASSERT_NE(drv, nullptr);
  ASSERT_EQ(drv->delays[0], 6u);

  d.Annotate(SdfLabel("(ABSOLUTE (cap 10))"));

  ASSERT_EQ(d.mgr.GetPrimitiveDrivers().size(), 1u);
  drv = d.Driver("z");
  ASSERT_NE(drv, nullptr);
  EXPECT_EQ(drv->delays[0], 30u);
}

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

  d.Annotate(SdfLabel("(ABSOLUTE (cap 10))"));
  EXPECT_EQ(d.mgr.GetPathDelay("a", "z"), 23u);
}

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

TEST(SdfSpecparamReevaluation, RealSpecparamTakesTheRealValue) {
  Design d;
  ASSERT_TRUE(
      d.Build("module m(input a, output z);\n"
              "  specify\n"
              "    specparam cap = 2.5;\n"
              "    (a => z) = 1.4 * cap + 0.7;\n"
              "  endspecify\n"
              "endmodule\n"));
  ASSERT_EQ(d.mgr.GetPathDelay("a", "z"), 4u);

  d.Annotate(SdfLabel("(ABSOLUTE (cap 1.5))"));

  EXPECT_EQ(d.mgr.GetPathDelay("a", "z"), 3u);
}

}  // namespace
