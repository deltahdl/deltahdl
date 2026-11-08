#include <gtest/gtest.h>

#include <string>

#include "fixture_sdf_design.h"
#include "fixture_simulator.h"
#include "fixture_specify_manager.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "simulator/evaluation.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_sdf.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

struct Design : SdfDesign {
  bool Build(const std::string& src) {
    if (!SdfDesign::Lower(src)) return false;
    const ModuleDecl& top = Top();
    mgr.BindDesignSpecparams(CollectDeclaredSpecparams(top), f.ctx, f.arena);
    mgr.BindDesignInterconnect(CollectInterconnectTopology(*cu, top));
    AddPathsAndTimingChecks(top);

    RegisterPathPulseSpecparams(top, f, mgr);
    return true;
  }

  SdfAnnotationResult Annotate(const std::string& sdf) {
    SdfFile file;
    EXPECT_TRUE(ParseSdf(sdf, file));
    return AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
  }

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

  const TimingCheckEntry* Check(TimingCheckKind kind) const {
    for (const auto& tc : mgr.GetTimingChecks()) {
      if (tc.kind == kind) return &tc;
    }
    return nullptr;
  }
};

std::string SdfCellText(const std::string& sections) {
  return "(DELAYFILE (CELL (CELLTYPE \"c\") (INSTANCE u1) " + sections + "))";
}

std::string SdfDelay(const std::string& body) {
  return SdfCellText("(DELAY (ABSOLUTE " + body + "))");
}

const char* const kLiteralPathSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kSpecparamPathSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    specparam cap = 12;\n"
    "    (A => Z) = cap;\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kModulePathpulseSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "    specparam PATHPULSE$ = (21, 34);\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kPathSpecificPathpulseSrc =
    "module c(input A, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "    specparam PATHPULSE$A$Z = (21, 34);\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kConditionalPathSrc =
    "module c(input A, input mode, output Z);\n"
    "  specify\n"
    "    (A => Z) = 40;\n"
    "    if (mode) (A => Z) = 50;\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kSpecparamCheckSrc =
    "module c(input D, input CK);\n"
    "  specify\n"
    "    specparam lim = 5;\n"
    "    $setup(D, posedge CK, lim);\n"
    "  endspecify\n"
    "endmodule\n";

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

TEST(SdfMultipleAnnotations, PathpulseThenIopathLosesTheAnnotatedPulseLimits) {
  Design d;
  ASSERT_TRUE(d.Build(kLiteralPathSrc));

  d.Annotate(SdfDelay("(PATHPULSE A Z (21) (34)) (IOPATH A Z (35) (61))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 35u);
  EXPECT_EQ(pd->delays[1], 61u);
  EXPECT_EQ(pd->reject_limit[0], 35u);
  EXPECT_EQ(pd->error_limit[0], 35u);
  EXPECT_EQ(pd->reject_limit[1], 61u);
  EXPECT_EQ(pd->error_limit[1], 61u);
}

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

TEST(SdfMultipleAnnotations, LaterIopathReplacesTheEarlierOneOnTheSamePath) {
  Design d;
  ASSERT_TRUE(d.Build(kLiteralPathSrc));

  d.Annotate(SdfDelay("(IOPATH A Z (35) (61)) (IOPATH A Z (7) (9))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 7u);
  EXPECT_EQ(pd->delays[1], 9u);
}

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

TEST(SdfMultipleAnnotations, IopathAfterLabelOverwritesTheReevaluatedDelay) {
  Design d;
  ASSERT_TRUE(d.Build(kSpecparamPathSrc));

  d.Annotate(SdfCellText(
      "(LABEL (ABSOLUTE (cap 30))) (DELAY (ABSOLUTE (IOPATH A Z (7))))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 7u);
  EXPECT_EQ(d.f.ctx.FindVariable("cap")->value.ToUint64(), 30u);
}

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

TEST(SdfMultipleAnnotations, TimingcheckAfterLabelUndoesTheReevaluation) {
  Design d;
  ASSERT_TRUE(d.Build(kSpecparamCheckSrc));

  d.Annotate(
      SdfCellText("(LABEL (ABSOLUTE (lim 40)))"
                  " (TIMINGCHECK (SETUP D (posedge CK) (20)))"));

  EXPECT_EQ(d.Check(TimingCheckKind::kSetup)->limit, 20u);
}

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

TEST(SdfMultipleAnnotations, UnannotatableEntryDoesNotDisturbTheRun) {
  Design d;
  ASSERT_TRUE(d.Build(kLiteralPathSrc));

  const auto kResult = d.Annotate(
      SdfDelay("(IOPATH A Z (35)) (NOSUCHENTRY A Z (99)) (IOPATH A Z (7))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 7u);

  bool warned = false;
  for (const auto& w : kResult.warnings) {
    if (w.find("NOSUCHENTRY") != std::string::npos) warned = true;
  }
  EXPECT_TRUE(warned);
}

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

TEST(SdfMultipleAnnotations, IncrementDeltypeInTheSameSectionModifies) {
  Design d;
  ASSERT_TRUE(d.Build(kLiteralPathSrc));

  const SdfAnnotationResult kResult =
      d.Annotate(SdfCellText("(DELAY (ABSOLUTE (IOPATH A Z (35) (61)))"
                             " (INCREMENT (IOPATH A Z (5) (5))))"));
  EXPECT_TRUE(kResult.warnings.empty());
  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 40u);
  EXPECT_EQ(pd->delays[1], 66u);
}

TEST(SdfMultipleAnnotations, NegativeIncrementLowersTheEarlierAnnotation) {
  Design d;
  ASSERT_TRUE(d.Build(kLiteralPathSrc));

  d.Annotate(
      SdfCellText("(DELAY (ABSOLUTE (IOPATH A Z (35) (61))))"
                  " (DELAY (INCREMENT (IOPATH A Z (-2) (-2))))"));
  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 33u);
  EXPECT_EQ(pd->delays[1], 59u);

  d.Annotate(SdfCellText("(DELAY (INCREMENT (IOPATH A Z (-40) (-2))))"));
  EXPECT_EQ(pd->delays[0], 0u);
  EXPECT_EQ(pd->delays[1], 57u);
}

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

TEST(SdfMultipleAnnotations, IncrementInterconnectAddsItsStatedLimits) {
  Design d;
  ASSERT_TRUE(d.Build(kThreeSourceSrc));

  d.Annotate(SdfCellText(
      "(DELAY (ABSOLUTE (INTERCONNECT i13/out i15/in ((10) (4) (6)))))"
      " (DELAY (INCREMENT (INTERCONNECT i13/out i15/in ((1) (2) (3)))))"));

  const auto* got = d.mgr.FindInterconnectDelay("i13/out", "i15/in");
  ASSERT_NE(got, nullptr);
  EXPECT_EQ(got->delays[0], 11u);
  EXPECT_EQ(got->reject_limit[0], 6u);
  EXPECT_EQ(got->error_limit[0], 9u);
}

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

TEST(SdfMultipleAnnotations, IncrementLabelModifiesTheEarlierLabel) {
  Design d;
  ASSERT_TRUE(d.Build(kSpecparamPathSrc));

  d.Annotate(
      SdfCellText("(LABEL (ABSOLUTE (cap 30))) (LABEL (INCREMENT (cap 5)))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 35u);
}

TEST(SdfMultipleAnnotations, IncrementLabelTypeInTheSameSectionModifies) {
  Design d;
  ASSERT_TRUE(d.Build(kSpecparamPathSrc));

  const SdfAnnotationResult kResult = d.Annotate(
      SdfCellText("(LABEL (ABSOLUTE (cap 30)) (INCREMENT (cap 5)))"));
  EXPECT_TRUE(kResult.warnings.empty());
  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 35u);
}

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

TEST(SdfMultipleAnnotations, PlainIopathDiscardsDeclaredModulePulseLimits) {
  Design d;
  ASSERT_TRUE(d.Build(kModulePathpulseSrc));

  d.Annotate(SdfDelay("(IOPATH A Z (35) (61))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 35u);
  EXPECT_EQ(pd->error_limit[0], 35u);
}

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

TEST(SdfMultipleAnnotations, EachDirectionsPulseLimitsReachItsTransitions) {
  Design d;
  ASSERT_TRUE(d.Build(kLiteralPathSrc));

  d.Annotate(SdfDelay("(IOPATH A Z ((10) (2) (3)) ((20) (4) (6)))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->reject_limit[0], 2u);
  EXPECT_EQ(pd->error_limit[0], 3u);
  EXPECT_EQ(pd->reject_limit[1], 4u);
  EXPECT_EQ(pd->error_limit[1], 6u);
}

TEST(SdfMultipleAnnotations, EmptySimpleValueHoldsTheCurrentDelay) {
  Design d;
  ASSERT_TRUE(d.Build(kLiteralPathSrc));

  d.Annotate(SdfDelay("(IOPATH A Z () (7))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 40u);
  EXPECT_EQ(pd->delays[1], 7u);
}

TEST(SdfMultipleAnnotations, EmptyDelayParenthesesHoldTheCurrentDelay) {
  Design d;
  ASSERT_TRUE(d.Build(kLiteralPathSrc));

  d.Annotate(SdfDelay("(IOPATH A Z (() (1) (2)) ((7)))"));

  const auto* pd = d.Path("A", "Z");
  ASSERT_NE(pd, nullptr);
  EXPECT_EQ(pd->delays[0], 40u);
  EXPECT_EQ(pd->delays[1], 7u);
  EXPECT_EQ(pd->reject_limit[0], 1u);
  EXPECT_EQ(pd->error_limit[0], 2u);
}

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
