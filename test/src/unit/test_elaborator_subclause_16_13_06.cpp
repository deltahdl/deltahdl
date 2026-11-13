#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/sampled_value.h"
#include "elaborator/sequence_method.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SequenceMethods, OperandMustBeNamedInstanceOrSequenceFormal) {
  EXPECT_TRUE(IsSequenceMethodOperandLegal(
      SequenceMethodOperandKind::kNamedSequenceInstance));
  EXPECT_TRUE(IsSequenceMethodOperandLegal(
      SequenceMethodOperandKind::kUntypedFormalArgument));
  EXPECT_TRUE(IsSequenceMethodOperandLegal(
      SequenceMethodOperandKind::kSequenceTypedFormalArgument));
  EXPECT_FALSE(IsSequenceMethodOperandLegal(SequenceMethodOperandKind::kOther));
}

TEST(SequenceMethods, ResultIsSingleBitAndStartPointIndependent) {
  EXPECT_TRUE(SequenceMethodResultIsSingleBit());
  EXPECT_FALSE(SequenceMethodResultDependsOnStartPoint());
}

TEST(SequenceMethods, TriggeredLegalInAssertionWaitAndBooleanContexts) {
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered, SequenceMethodContext::kAssertionStatement,
      false));
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered, SequenceMethodContext::kWaitStatement,
      false));
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered,
      SequenceMethodContext::kBooleanExpressionOutsideSequence, false));
}

TEST(SequenceMethods, TriggeredOutsideSequenceWithLocalVarFormalIsError) {
  EXPECT_FALSE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered,
      SequenceMethodContext::kBooleanExpressionOutsideSequence, true));
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered, SequenceMethodContext::kSequenceExpression,
      true));
}

TEST(SequenceMethods, TriggeredInAssertionStaysLegalWithLocalVarFormal) {
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered, SequenceMethodContext::kAssertionStatement,
      true));
  EXPECT_FALSE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered, SequenceMethodContext::kWaitStatement, true));
}

TEST(SequenceMethods, FormalIsLocalVarWhenUsedAsMatchItemLvalue) {
  EXPECT_TRUE(SequenceTreatsFormalAsLocalVar(true));
  EXPECT_FALSE(SequenceTreatsFormalAsLocalVar(false));
}

TEST(SequenceMethods, MatchedLegalOnlyInSequenceExpressions) {
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kMatched, SequenceMethodContext::kSequenceExpression,
      false));
  EXPECT_FALSE(IsSequenceMethodContextLegal(
      SequenceMethod::kMatched, SequenceMethodContext::kAssertionStatement,
      false));
  EXPECT_FALSE(IsSequenceMethodContextLegal(
      SequenceMethod::kMatched, SequenceMethodContext::kWaitStatement, false));
  EXPECT_FALSE(IsSequenceMethodContextLegal(
      SequenceMethod::kMatched,
      SequenceMethodContext::kBooleanExpressionOutsideSequence, false));
}

TEST(SequenceMethods, StatusSetInObservedRegionAndSampledAsCurrentValue) {
  EXPECT_TRUE(SequenceMethodStatusSetInObservedRegion());
  EXPECT_TRUE(SequenceMethodSampledValueIsCurrentValue());
}

TEST(SequenceMethods, PersistenceDiffersBetweenTriggeredAndMatched) {
  EXPECT_EQ(SequenceMethodStatusPersistence(SequenceMethod::kTriggered),
            SequenceMethodPersistence::kThroughTimeStep);
  EXPECT_EQ(SequenceMethodStatusPersistence(SequenceMethod::kMatched),
            SequenceMethodPersistence::kUntilFirstDestinationClockTick);
}

TEST(SequenceMethods, EmptyMatchDoesNotActivateMethods) {
  EXPECT_FALSE(EmptyMatchActivatesSequenceMethod());
}

TEST(SequenceMethods, TriggeredDependenciesMustBeAcyclic) {
  const std::vector<std::pair<int, int>> kChain = {{0, 1}, {1, 2}};
  EXPECT_TRUE(TriggeredSequenceDependenciesAreAcyclic(3, kChain));
  const std::vector<std::pair<int, int>> kCycle = {{0, 1}, {1, 0}};
  EXPECT_FALSE(TriggeredSequenceDependenciesAreAcyclic(2, kCycle));
  const std::vector<std::pair<int, int>> kSelfLoop = {{0, 0}};
  EXPECT_FALSE(TriggeredSequenceDependenciesAreAcyclic(1, kSelfLoop));
}

TEST(SequenceMethods,
     TriggeredDependencyCycleDetectionHandlesChainsAndDiamonds) {
  const std::vector<std::pair<int, int>> kLongCycle = {{0, 1}, {1, 2}, {2, 0}};
  EXPECT_FALSE(TriggeredSequenceDependenciesAreAcyclic(3, kLongCycle));
  const std::vector<std::pair<int, int>> kDiamond = {
      {0, 1}, {0, 2}, {1, 3}, {2, 3}};
  EXPECT_TRUE(TriggeredSequenceDependenciesAreAcyclic(4, kDiamond));
  EXPECT_TRUE(TriggeredSequenceDependenciesAreAcyclic(3, {}));
}

TEST(SequenceMethods, ClockInferredFromContextUnlessExplicitlyClocked) {
  EXPECT_FALSE(SequenceMethodClockIsInferredFromContext(
      SequenceMethodClockContext::kExplicitlyClocked));
  EXPECT_TRUE(SequenceMethodClockIsInferredFromContext(
      SequenceMethodClockContext::kCheckerInstantiation));
  EXPECT_TRUE(SequenceMethodClockIsInferredFromContext(
      SequenceMethodClockContext::kModulePortConnection));
  EXPECT_TRUE(SequenceMethodClockIsInferredFromContext(
      SequenceMethodClockContext::kInterfaceOrProgramPortConnection));
  EXPECT_TRUE(SequenceMethodClockIsInferredFromContext(
      SequenceMethodClockContext::kFunctionOrTaskArgument));
  EXPECT_TRUE(SequenceMethodClockIsInferredFromContext(
      SequenceMethodClockContext::kEventExpressionInstance));
  EXPECT_TRUE(SequenceMethodClockIsInferredFromContext(
      SequenceMethodClockContext::kInferredFromSurroundingContext));
}

TEST(SequenceMethods, InferredClockDefaultAppliesWhenNoActualArgument) {
  EXPECT_TRUE(InferredClockDefaultUsesSampledValueRules(false));
  EXPECT_FALSE(InferredClockDefaultUsesSampledValueRules(true));
}

TEST(SequenceMethods, MatchedInSampledValueFunctionIsError) {
  EXPECT_FALSE(SampledValueArgumentIsLegal(false, true));
  EXPECT_TRUE(SampledValueArgumentIsLegal(false, false));
}

TEST(SequenceMethods, GeneralClockInferenceReusesSampledValueRules) {
  EXPECT_TRUE(SequenceMethodClockIsInferredFromContext(
      SequenceMethodClockContext::kInferredFromSurroundingContext));
  EXPECT_EQ(InferSampledValueClockingEvent(
                SampledValueClockContext::kOutsideAssertion),
            SampledValueClockInference::kFromDefaultClocking);
  EXPECT_EQ(InferSampledValueClockingEvent(
                SampledValueClockContext::kAssertionSequenceOrProperty),
            SampledValueClockInference::kFromClockFlow);
}

TEST(SequenceMethods, TriggeredOfAnUnclockedSequenceInADisableIsReported) {
  const char* const kReport =
      "triggered of the sequence 's', which has no explicit clocking event, "
      "may not stand in a disable condition";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  sequence s;\n"
      "    a ##1 b;\n"
      "  endsequence\n"
      "  sequence t;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  a1: assert property (@(posedge clk) disable iff (s.triggered) c);\n"
      "  a2: assert property (@(posedge clk) disable iff (t.triggered) c);\n"
      "  event ev;\n"
      "  a3: assert property (@(posedge clk) disable iff (ev.triggered) c);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 9, "16.13.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "triggered of the sequence",
                             12, "16.13.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "triggered of the sequence",
                             10, "16.13.6"));
}

TEST(SequenceMethods, TriggeredOutsideASequenceOnAnAssigningOneIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  int v;\n"
      "  sequence s(lv);\n"
      "    @(posedge clk) (a, lv = 1) ##1 a;\n"
      "  endsequence\n"
      "  sequence t;\n"
      "    int w;\n"
      "    @(posedge clk) a ##1 s(w).triggered;\n"
      "  endsequence\n"
      "  initial wait (s(v).triggered);\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "triggered may not be applied outside a sequence expression to 's'";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 11, "16.13.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 9, "16.13.6"));
}

TEST(SequenceMethods, ACycleThroughTriggeredIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  sequence s1;\n"
      "    @(posedge clk) a ##1 s2.triggered;\n"
      "  endsequence\n"
      "  sequence s2;\n"
      "    @(posedge clk) a ##1 s1.triggered;\n"
      "  endsequence\n"
      "  sequence s3;\n"
      "    @(posedge clk) a ##1 s4.triggered;\n"
      "  endsequence\n"
      "  sequence s4;\n"
      "    @(posedge clk) s5 ##1 s5;\n"
      "  endsequence\n"
      "  sequence s5;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the sequence 's1' depends on its own end point "
                            "through triggered",
                            3, "16.13.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "the sequence 's3' depends on its own end point",
                             9, "16.13.6"));
}

TEST(SequenceMethods, MatchedOutsideASequenceIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, x;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 a;\n"
      "  endsequence\n"
      "  initial wait (s.matched);\n"
      "  always @(posedge clk) x <= s.matched;\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "matched may be used only in a sequence expression";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 6, "16.13.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 7, "16.13.6"));
}

constexpr const char* kMethodSignals =
    "  bit clk, a, x;\n"
    "  logic z;\n"
    "  int v, v2;\n";

std::string Replaced(std::string text, const std::string& actual) {
  for (size_t at = text.find('%'); at != std::string::npos;
       at = text.find('%', at + actual.size())) {
    text.replace(at, 1, actual);
  }
  return text;
}

std::string MethodPlaceSource(const std::string& place,
                              const std::string& declarations,
                              const std::string& items) {
  std::string signals = kMethodSignals;
  std::string instance = "module m;\n  w u();\nendmodule\n";
  if (place == "module") {
    return "module m;\n" + signals + declarations + items + "endmodule\n";
  }
  if (place == "if generate") {
    return "module m;\n" + signals + declarations + "  if (1) begin : g\n" +
           items + "  end\nendmodule\n";
  }
  if (place == "if generate declaring") {
    return "module m;\n" + signals + "  if (1) begin : g\n" + declarations +
           items + "  end\nendmodule\n";
  }
  if (place == "for generate") {
    return "module m;\n" + signals +
           "  for (genvar i = 0; i < 1; i++) begin : g\n" + declarations +
           items + "  end\nendmodule\n";
  }
  if (place == "package") {
    return "package pk;\n" + signals + declarations +
           "endpackage\nmodule m;\n  import pk::*;\n  logic z;\n" + items +
           "endmodule\n";
  }
  if (place == "compilation unit") {
    return signals + declarations + "module m;\n  logic z;\n" + items +
           "endmodule\n";
  }
  if (place == "checker") {
    return "checker w;\n" + signals + declarations + items + "endchecker\n" +
           instance;
  }
  return place + " w;\n" + signals + declarations + items + "end" + place +
         "\n" + instance;
}

constexpr const char* kAssigningReport =
    "triggered may not be applied outside a sequence expression to 's'";

struct AssigningForm {
  const char* declaration;
  const char* instance;
};

constexpr AssigningForm kAssigningForms[] = {
    {"(lv); @(posedge clk) (a, lv = 1) ##1 a;", "s(%)"},
    {"(untyped lv); @(posedge clk) (a, lv = 1) ##1 a;", "s(%)"},
    {"(local output int lv); @(posedge clk) (a, lv = 1) ##1 a;", "s(%)"},
    {"(lv); int y; @(posedge clk) (a, y = 0, lv = 1) ##1 a;", "s(%)"},
    {"(lv); @(posedge clk) ((a, lv = 1) ##1 a) ##1 a;", "s(%)"},
    {"(lv); @(posedge clk) first_match((a, lv = 1) ##1 a);", "s(%)"},
    {"(lv); @(posedge clk) (a, lv = 1) ##1 a or a ##1 a;", "s(%)"},
    {"(lv); @(posedge clk) (a, lv = 1) ##1 a intersect a ##1 a;", "s(%)"},
    {"(lv); @(posedge clk) (a, lv = 1)[*2];", "s(%)"}};

constexpr AssigningForm kReadingAssigningForms[] = {
    {"(lv); @(posedge clk) (a, lv += 1) ##1 a;", "s(%)"},
    {"(lv); @(posedge clk) (a, lv -= 1) ##1 a;", "s(%)"},
    {"(lv); @(posedge clk) (a, lv *= 2) ##1 a;", "s(%)"},
    {"(lv); @(posedge clk) (a, lv /= 2) ##1 a;", "s(%)"},
    {"(lv); @(posedge clk) (a, lv %= 2) ##1 a;", "s(%)"},
    {"(lv); @(posedge clk) (a, lv &= 1) ##1 a;", "s(%)"},
    {"(lv); @(posedge clk) (a, lv |= 1) ##1 a;", "s(%)"},
    {"(lv); @(posedge clk) (a, lv ^= 1) ##1 a;", "s(%)"},
    {"(lv); @(posedge clk) (a, lv <<= 1) ##1 a;", "s(%)"},
    {"(lv); @(posedge clk) (a, lv >>= 1) ##1 a;", "s(%)"},
    {"(lv); @(posedge clk) (a, lv <<<= 1) ##1 a;", "s(%)"},
    {"(lv); @(posedge clk) (a, lv >>>= 1) ##1 a;", "s(%)"},
    {"(lv); @(posedge clk) (a, lv++) ##1 a;", "s(%)"},
    {"(lv); @(posedge clk) (a, lv--) ##1 a;", "s(%)"},
    {"(lv); @(posedge clk) (a, ++lv) ##1 a;", "s(%)"},
    {"(lv); @(posedge clk) (a, --lv) ##1 a;", "s(%)"}};

std::string AssigningDeclaration(const AssigningForm& form) {
  return "  sequence s" + std::string(form.declaration) + " endsequence\n";
}

void ExpectAssigningFormReportedInAWait(const AssigningForm& form,
                                        bool accepted_inside) {
  std::string read =
      "  initial wait (" + Replaced(form.instance, "v") + ".triggered);\n";
  std::string inside = "  sequence t; int w; @(posedge clk) (a, w = 0) ##1 " +
                       Replaced(form.instance, "w") +
                       ".triggered; endsequence\n";
  std::string src =
      MethodPlaceSource("module", AssigningDeclaration(form) + inside, read);
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kAssigningReport,
                            LineHolding(src, "initial wait"), "16.13.6"));
  if (accepted_inside) {
    EXPECT_FALSE(
        ErrorOnLine(f.diag.Diagnostics(), LineHolding(src, "sequence t;")));
  }
}

TEST(TriggeredOnAnAssigningSequence,
     EachMatchItemAssignmentOfAFormalIsReportedOutsideASequence) {
  for (const AssigningForm& form : kAssigningForms) {
    ExpectAssigningFormReportedInAWait(form, true);
  }
  for (const AssigningForm& form : kReadingAssigningForms) {
    ExpectAssigningFormReportedInAWait(form, false);
  }
}

constexpr const char* kAssigningSequence =
    "  sequence s(lv); @(posedge clk) (a, lv = 1) ##1 a; endsequence\n";

constexpr const char* kProceduralReads[] = {
    "  initial wait (s(v).triggered);\n",
    "  initial if (s(v).triggered) x = 1;\n",
    "  initial x = s(v).triggered ? 1 : 0;\n",
    "  always_comb x = s(v).triggered;\n",
    "  task tk; wait (s(v).triggered); endtask\n",
    "  function bit fn; return s(v).triggered; endfunction\n",
    "  final $display(s(v).triggered);\n"};

void ExpectAssigningReadsReportedIn(const std::string& place,
                                    const std::string& declarations,
                                    const std::string& read) {
  std::string src = MethodPlaceSource(place, declarations, read);
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kAssigningReport,
                            LineHolding(src, read.substr(2, 12)), "16.13.6"));
}

TEST(TriggeredOnAnAssigningSequence, EachProceduralReadIsReported) {
  for (const char* read : kProceduralReads) {
    ExpectAssigningReadsReportedIn("module", kAssigningSequence, read);
  }
}

TEST(TriggeredOnAnAssigningSequence,
     AReadIsReportedInAnInterfaceAProgramAndAChecker) {
  ExpectAssigningReadsReportedIn("interface", kAssigningSequence,
                                 kProceduralReads[0]);
  ExpectAssigningReadsReportedIn("program", kAssigningSequence,
                                 kProceduralReads[0]);
  ExpectAssigningReadsReportedIn("checker", kAssigningSequence,
                                 kProceduralReads[3]);
}

constexpr const char* kContinuousReads[] = {"  assign z = s(v).triggered;\n",
                                            "  wire wn = s(v).triggered;\n"};

TEST(TriggeredOnAnAssigningSequence,
     DISABLED_AContinuousAndANetDeclarationAssignmentAreReported) {
  for (const char* read : kContinuousReads) {
    ExpectAssigningReadsReportedIn("module", kAssigningSequence, read);
  }
}

TEST(TriggeredOnAnAssigningSequence,
     DISABLED_AReadIsReportedInAGenerateBlockAPackageAndTheCompilationUnit) {
  for (const char* place :
       {"if generate", "for generate", "package", "compilation unit"}) {
    ExpectAssigningReadsReportedIn(place, kAssigningSequence,
                                   kProceduralReads[0]);
  }
  ExpectAssigningReadsReportedIn("package", kAssigningSequence,
                                 "  initial wait (pk::s(pk::v).triggered);\n");
  std::string src = "package pk;\n" + std::string(kMethodSignals) +
                    kAssigningSequence +
                    "  function bit fn; return s(v).triggered; endfunction\n"
                    "endpackage\n"
                    "module m;\nendmodule\n";
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kAssigningReport,
                            LineHolding(src, "function bit fn"), "16.13.6"));
}

constexpr const char* kNonAssigningSequences =
    "  sequence r(lv); int w; @(posedge clk) (a, w = lv) ##1 a; endsequence\n"
    "  sequence q; int w; @(posedge clk) (a, w = 1) ##1 a; endsequence\n";

constexpr const char* kAllowedReads[] = {
    ("  initial wait (r(v).triggered);\n", "  assign z = r(v).triggered;\n"),
    "  initial wait (q.triggered);\n",
    "  a1: assert property (@(posedge clk) s(v).triggered);\n",
    "  a2: assert property (@(posedge clk) a |-> s(v).triggered);\n"};

TEST(TriggeredOnAnAssigningSequence,
     ANonAssigningSequenceAndAnAssertionReadAreAccepted) {
  for (const char* read : kAllowedReads) {
    std::string src = MethodPlaceSource(
        "module", std::string(kAssigningSequence) + kNonAssigningSequences,
        read);
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_EQ(f.diag.ErrorCount(), 0u);
  }
}

struct TriggeredCycle {
  const char* declarations;
  const char* reported[3];
  const char* accepted[4];
};

std::string CycleReport(const std::string& name) {
  return "the sequence '" + name +
         "' depends on its own end point through "
         "triggered";
}

void ExpectCyclesJudgedIn(const std::string& place,
                          const TriggeredCycle& cycle) {
  std::string src = MethodPlaceSource(place, cycle.declarations, "");
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  for (const char* name : cycle.reported) {
    if (name == nullptr) break;
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), CycleReport(name),
                              LineHolding(src, "sequence " + std::string(name)),
                              "16.13.6"));
  }
  for (const char* name : cycle.accepted) {
    if (name == nullptr) break;
    EXPECT_FALSE(
        ErrorOnLine(f.diag.Diagnostics(),
                    LineHolding(src, "sequence " + std::string(name))));
  }
}

constexpr TriggeredCycle kModuleCycles[] = {
    {"  sequence s0; @(posedge clk) a ##1 a; endsequence\n"
     "  sequence s1; @(posedge clk) a ##1 s1.triggered; endsequence\n"
     "  sequence r1; @(posedge clk) a ##1 s0.triggered; endsequence\n",
     {"s1"},
     {"r1", "s0"}},
    {"  sequence s2; @(posedge clk) a ##1 s3.triggered; endsequence\n"
     "  sequence s3; @(posedge clk) a ##1 s4.triggered; endsequence\n"
     "  sequence s4; @(posedge clk) a ##1 s2.triggered; endsequence\n"
     "  sequence r2; @(posedge clk) a ##1 r3.triggered; endsequence\n"
     "  sequence r3; @(posedge clk) a ##1 r4.triggered; endsequence\n"
     "  sequence r4; @(posedge clk) a ##1 a; endsequence\n",
     {"s2", "s3", "s4"},
     {"r2", "r3", "r4"}},
    {"  sequence s5(x); @(posedge clk) x ##1 s6(a).triggered; endsequence\n"
     "  sequence s6(y); @(posedge clk) y ##1 s5(y).triggered; endsequence\n"
     "  sequence r5(x); @(posedge clk) x ##1 r6(a).triggered; endsequence\n"
     "  sequence r6(y); @(posedge clk) y ##1 y; endsequence\n",
     {"s5", "s6"},
     {"r5", "r6"}},
    {"  sequence s7; @(posedge clk) a ##1 s8; endsequence\n"
     "  sequence s8; @(posedge clk) a ##1 s7.triggered; endsequence\n"
     "  sequence r7; @(posedge clk) a ##1 a; endsequence\n"
     "  sequence r8; @(posedge clk) a ##1 r7.triggered; endsequence\n",
     {"s8"},
     {"r7", "r8"}},
    {"  sequence d1; @(posedge clk) a ##1 a; endsequence\n"
     "  sequence d2; @(posedge clk) a ##1 d1.triggered; endsequence\n"
     "  sequence d3; @(posedge clk) a ##2 d1.triggered; endsequence\n"
     "  sequence d4; @(posedge clk) d2.triggered ##1 d3.triggered; "
     "endsequence\n",
     {},
     {"d1", "d2", "d3", "d4"}},
    {"  sequence o1; @(posedge clk) a ##1 a; endsequence\n"
     "  property p1; @(posedge clk) a |-> o1.triggered; endproperty\n"
     "  initial wait (o1.triggered);\n"
     "  a1: assert property (p1);\n",
     {},
     {"o1"}}};

TEST(TriggeredCycleElaboration, EachCycleInAModuleIsReportedBesideItsOpenForm) {
  for (const TriggeredCycle& cycle : kModuleCycles) {
    ExpectCyclesJudgedIn("module", cycle);
  }
}

constexpr TriggeredCycle kCyclesThroughFormals[] = {
    {"  sequence s0; @(posedge clk) a ##1 a; endsequence\n"
     "  sequence w(sequence q); @(posedge clk) a ##1 q.triggered; "
     "endsequence\n"
     "  sequence s; @(posedge clk) a ##1 w(s); endsequence\n"
     "  sequence r; @(posedge clk) a ##1 w(s0); endsequence\n",
     {"s"},
     {"r", "w", "s0"}},
    {"  sequence s0; @(posedge clk) a ##1 a; endsequence\n"
     "  sequence u(q); @(posedge clk) a ##1 q.triggered; endsequence\n"
     "  sequence t; @(posedge clk) a ##1 u(t); endsequence\n"
     "  sequence r; @(posedge clk) a ##1 u(s0); endsequence\n",
     {"t"},
     {"r", "u", "s0"}}};

TEST(TriggeredCycleElaboration,
     DISABLED_ACycleThroughASequenceOrUntypedFormalIsReported) {
  for (const TriggeredCycle& cycle : kCyclesThroughFormals) {
    ExpectCyclesJudgedIn("module", cycle);
  }
}

constexpr TriggeredCycle kScopeCycle = {
    "  sequence s1; @(posedge clk) a ##1 s2.triggered; endsequence\n"
    "  sequence s2; @(posedge clk) a ##1 s1.triggered; endsequence\n"
    "  sequence o1; @(posedge clk) a ##1 o2.triggered; endsequence\n"
    "  sequence o2; @(posedge clk) a ##1 a; endsequence\n",
    {"s1", "s2"},
    {"o1", "o2"}};

TEST(TriggeredCycleElaboration,
     ACycleIsReportedInAnInterfaceAProgramAndAChecker) {
  for (const char* place : {"interface", "program", "checker"}) {
    ExpectCyclesJudgedIn(place, kScopeCycle);
  }
}

TEST(TriggeredCycleElaboration,
     DISABLED_ACycleIsReportedInAGenerateBlockAPackageAndTheCompilationUnit) {
  for (const char* place : {"if generate declaring", "for generate", "package",
                            "compilation unit"}) {
    ExpectCyclesJudgedIn(place, kScopeCycle);
  }
  ExpectCyclesJudgedIn(
      "for generate",
      {"  sequence g3; @(posedge clk) a ##1 g3.triggered; endsequence\n",
       {"g3"},
       {}});
}

constexpr const char* kMatchedReport =
    "matched may be used only in a sequence expression";

constexpr const char* kMatchedSource =
    "  sequence s; @(posedge clk) a ##1 a; endsequence\n";

constexpr const char* kMatchedNeighbours =
    "module sub(input logic p);\nendmodule\n"
    "module hold;\n"
    "  bit clk, a;\n"
    "  sequence s; @(posedge clk) a ##1 a; endsequence\n"
    "endmodule\n"
    "package pk;\n"
    "  bit clk, a;\n"
    "  sequence ps; @(posedge clk) a ##1 a; endsequence\n"
    "endpackage\n";

void ExpectMatchedReportedIn(const std::string& place,
                             const std::string& declarations,
                             const std::string& read) {
  std::string src =
      kMatchedNeighbours + MethodPlaceSource(place, declarations, read);
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMatchedReport,
                            LineHolding(src, ".matched"), "16.13.6"));
}

constexpr const char* kReportedMatchedReads[] = {
    "  always_comb z = s.matched;\n",
    "  always_latch if (s.matched) z = 1;\n",
    "  final $display(s.matched);\n",
    "  initial x = s.matched ? 1 : 0;\n",
    ("  function bit f(bit b); return b; endfunction\n"
     "  initial x = f(s.matched);\n"),
    "  task tk; wait (s.matched); endtask\n",
    "  initial x = pk::ps.matched;\n",
    "  hold u();\n  initial x = u.s.matched;\n"};

TEST(MatchedOutsideASequence, EachProceduralReadInAModuleIsReported) {
  for (const char* read : kReportedMatchedReads) {
    ExpectMatchedReportedIn("module", kMatchedSource, read);
  }
}

TEST(MatchedOutsideASequence,
     AProceduralReadIsReportedInAnInterfaceAProgramAndAChecker) {
  ExpectMatchedReportedIn("interface", kMatchedSource,
                          "  initial x = s.matched;\n");
  ExpectMatchedReportedIn("program", kMatchedSource,
                          "  initial x = s.matched;\n");
  ExpectMatchedReportedIn("checker", kMatchedSource,
                          "  always_ff @(posedge clk) x <= s.matched;\n");
}

constexpr const char* kUnreportedMatchedReads[] = {
    "  assign z = s.matched;\n",
    "  wire wn = s.matched;\n",
    "  initial @(s.matched) x = 1;\n",
    "  always @(s.matched) x = 1;\n",
    "  initial @(posedge clk iff s.matched) x = 1;\n",
    "  initial @(s.matched or posedge clk) x = 1;\n",
    "  sub u(s.matched);\n",
    "  hold u();\n  assign z = u.s.matched;\n"};

TEST(MatchedOutsideASequence,
     DISABLED_AContinuousReadAnEventControlAndAPortAreReported) {
  for (const char* read : kUnreportedMatchedReads) {
    ExpectMatchedReportedIn("module", kMatchedSource, read);
  }
}

TEST(MatchedOutsideASequence,
     DISABLED_AContinuousAssignmentIsReportedInEachOtherDesignUnit) {
  for (const char* place : {"interface", "program", "checker"}) {
    ExpectMatchedReportedIn(place, kMatchedSource, "  assign z = s.matched;\n");
  }
}

TEST(MatchedOutsideASequence, DISABLED_AReadIsReportedInAGenerateBlock) {
  for (const char* place :
       {"if generate", "if generate declaring", "for generate"}) {
    ExpectMatchedReportedIn(place, kMatchedSource,
                            "  initial x = s.matched;\n");
    ExpectMatchedReportedIn(place, kMatchedSource, "  assign z = s.matched;\n");
  }
}

constexpr const char* kAllowedMatchedReads[] = {
    "  a1: assert property (@(posedge clk2) b |-> s.matched);\n",
    "  a2: assert property (@(posedge clk2) s.matched);\n",
    "  c1: cover sequence (@(posedge clk2) b ##1 s.matched);\n",
    ("  sequence e6(f); @(posedge clk2) b ##1 f; endsequence\n"
     "  a3: assert property (e6(s.matched));\n"),
    ("  sequence sa(sequence q); @(posedge clk2) b ##1 q.matched; "
     "endsequence\n"
     "  a4: assert property (sa(s));\n"),
    ("  sequence e3; @(posedge clk2) b ##1 s.matched ##1 b; endsequence\n"
     "  a5: assert property (e3);\n")};

TEST(MatchedOutsideASequence, MatchedInASequenceExpressionIsAccepted) {
  for (const char* read : kAllowedMatchedReads) {
    std::string src = MethodPlaceSource(
        "module", std::string(kMatchedSource) + "  bit clk2, b;\n", read);
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_EQ(f.diag.ErrorCount(), 0u);
  }
}

constexpr const char* kOperandDeclarations =
    "  event ev;\n"
    "  property p; @(posedge clk) a |=> a; endproperty\n"
    "  property pp(q); @(posedge clk) q |=> q; endproperty\n"
    "  sequence s; @(posedge clk) a ##1 a; endsequence\n"
    "  sequence sp(q); @(posedge clk) q ##1 q; endsequence\n";

struct OperandForm {
  const char* place;
  const char* declarations;
  const char* items;
  const char* method;
};

struct OperandPair {
  OperandForm forbidden;
  OperandForm allowed;
};

std::string OperandReport(const std::string& method) {
  return "the operand of " + method +
         " is not a sequence instance or an untyped or sequence formal "
         "argument";
}

std::string OperandSource(const OperandForm& form) {
  return MethodPlaceSource(
      form.place, kOperandDeclarations + std::string(form.declarations),
      form.items);
}

void ExpectOperandsJudged(const OperandPair& pair) {
  std::string forbidden = OperandSource(pair.forbidden);
  std::string method = pair.forbidden.method;
  SCOPED_TRACE(forbidden);
  ElabFixture f;
  ElaborateSrc(forbidden, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), OperandReport(method),
                            LineHolding(forbidden, "." + method), "16.13.6"));
  std::string allowed = OperandSource(pair.allowed);
  SCOPED_TRACE(allowed);
  ElabFixture g;
  ElaborateSrc(allowed, g);
  EXPECT_EQ(g.diag.ErrorCount(), 0u);
}

constexpr OperandPair InModule(const char* items_forbidden,
                               const char* items_allowed, const char* method) {
  return {{"module", "", items_forbidden, method},
          {"module", "", items_allowed, method}};
}

constexpr OperandPair kForbiddenOperands[] = {
    InModule("  sequence t; @(posedge clk) a ##1 p.triggered; endsequence\n",
             "  sequence t; @(posedge clk) a ##1 s.triggered; endsequence\n",
             "triggered"),
    InModule("  sequence t; @(posedge clk) a ##1 p.matched; endsequence\n",
             "  sequence t; @(posedge clk) a ##1 s.matched; endsequence\n",
             "matched"),
    InModule("  a1: assert property (@(posedge clk) a ##1 p.triggered);\n",
             "  a1: assert property (@(posedge clk) a ##1 s.triggered);\n",
             "triggered"),
    InModule("  a1: assert property (@(posedge clk) a ##1 p.matched);\n",
             "  a1: assert property (@(posedge clk) a ##1 s.matched);\n",
             "matched"),
    InModule("  initial wait (p.triggered);\n",
             "  initial wait (s.triggered);\n", "triggered"),
    InModule("  always @(posedge clk) if (p.triggered) x <= 1;\n",
             "  always @(posedge clk) if (s.triggered) x <= 1;\n", "triggered"),
    {{"package",
      "  sequence t; @(posedge clk) a ##1 pp(a).triggered; endsequence\n", "",
      "triggered"},
     {"package",
      "  sequence t; @(posedge clk) a ##1 sp(a).triggered; endsequence\n", "",
      "triggered"}},
    {{"if generate declaring", "",
      "  sequence t; @(posedge clk) a ##1 p.matched; endsequence\n", "matched"},
     {"if generate declaring", "",
      "  sequence t; @(posedge clk) a ##1 s.matched; endsequence\n",
      "matched"}},
    InModule("  a1: assert property (@(posedge clk) a ##1 v.matched);\n",
             "  a1: assert property (@(posedge clk) a ##1 s.matched);\n",
             "matched"),
    InModule("  a1: assert property (@(posedge clk) a ##1 v.triggered);\n",
             "  a1: assert property (@(posedge clk) a ##1 s.triggered);\n",
             "triggered"),
    {{"interface", "",
      "  sequence t; @(posedge clk) a ##1 v.triggered; endsequence\n",
      "triggered"},
     {"interface", "",
      "  sequence t; @(posedge clk) a ##1 s.triggered; endsequence\n",
      "triggered"}},
    {{"interface", "",
      "  sequence t; @(posedge clk) a ##1 v.matched; endsequence\n", "matched"},
     {"interface", "",
      "  sequence t; @(posedge clk) a ##1 s.matched; endsequence\n",
      "matched"}},
    InModule("  a1: assert property (@(posedge clk) a ##1 ev.matched);\n",
             "  a1: assert property (@(posedge clk) a ##1 s.matched);\n",
             "matched"),
    InModule("  sequence d6(int q); @(posedge clk) a ##1 q.matched; "
             "endsequence\n",
             "  sequence d6(sequence q); @(posedge clk) a ##1 q.matched; "
             "endsequence\n",
             "matched"),
    InModule("  sequence d6(bit q); @(posedge clk) a ##1 q.matched; "
             "endsequence\n"
             "  a1: assert property (d6(x));\n",
             "  sequence d6(sequence q); @(posedge clk) a ##1 q.matched; "
             "endsequence\n"
             "  a1: assert property (d6(s));\n",
             "matched"),
    InModule("  property pe(event e); @(posedge clk) a |-> e.matched; "
             "endproperty\n",
             "  property pe(sequence e); @(posedge clk) a |-> e.matched; "
             "endproperty\n",
             "matched"),
    InModule("  property pq(property q); @(posedge clk) a |-> q.triggered; "
             "endproperty\n",
             "  property pq(sequence q); @(posedge clk) a |-> q.triggered; "
             "endproperty\n",
             "triggered"),
    InModule("  checker ck(property q, event e);\n"
             "    a1: assert property (@e a ##1 q.triggered);\n"
             "  endchecker\n"
             "  ck c1(p, posedge clk);\n",
             "  checker ck(sequence q, event e);\n"
             "    a1: assert property (@e a ##1 q.triggered);\n"
             "  endchecker\n"
             "  ck c1(s, posedge clk);\n",
             "triggered")};

TEST(SequenceMethodOperand,
     DISABLED_EachOperandButASequenceInstanceOrFormalIsReported) {
  for (const OperandPair& pair : kForbiddenOperands) {
    ExpectOperandsJudged(pair);
  }
}

}  // namespace
