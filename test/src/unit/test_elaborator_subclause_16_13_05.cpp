#include <gtest/gtest.h>

#include <initializer_list>
#include <string>

#include "elaborator/multiclock_endpoint.h"
#include "elaborator/sequence_method.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(MulticlockEndPoint, TriggeredEndingClockMustMatchContextClock) {
  EXPECT_TRUE(TriggeredEndingClockMatchesContext("clk", "clk"));
  EXPECT_FALSE(TriggeredEndingClockMatchesContext("clk0", "clk1"));
}

TEST(MulticlockEndPoint, MatchedDetectsEndPointWhenClocksDiffer) {
  EXPECT_TRUE(MatchedDetectsCrossClockEndPoint("clk", "sysclk"));
  EXPECT_FALSE(MatchedDetectsCrossClockEndPoint("clk", "clk"));
}

TEST(MulticlockEndPoint, MatchedOperandMustBeNamedInstanceOrSequenceFormal) {
  EXPECT_TRUE(IsSequenceMethodOperandLegal(
      SequenceMethodOperandKind::kNamedSequenceInstance));
  EXPECT_TRUE(IsSequenceMethodOperandLegal(
      SequenceMethodOperandKind::kUntypedFormalArgument));
  EXPECT_TRUE(IsSequenceMethodOperandLegal(
      SequenceMethodOperandKind::kSequenceTypedFormalArgument));
  EXPECT_FALSE(IsSequenceMethodOperandLegal(SequenceMethodOperandKind::kOther));
}

TEST(MulticlockEndPoint, MatchedResultIsSingleBitAndStartPointIndependent) {
  EXPECT_TRUE(SequenceMethodResultIsSingleBit());
  EXPECT_FALSE(SequenceMethodResultDependsOnStartPoint());
}

TEST(MulticlockEndPoint, MatchedSupportsFormalsAndSharesLocalVarRules) {
  EXPECT_TRUE(MatchedAllowedOnSequenceWithFormalArguments());
  EXPECT_TRUE(MatchedLocalVariableRulesSameAsTriggered());
}

TEST(MulticlockEndPoint, MatchedMultipleMatchesActLikeOrDisjuncts) {
  EXPECT_TRUE(MatchedMultipleMatchesTreatedAsOrDisjuncts());
}

TEST(MulticlockEndPoint, MatchedSynchronizesAcrossClocks) {
  EXPECT_TRUE(MatchedSynchronizesAcrossClocks());
  EXPECT_EQ(SequenceMethodStatusPersistence(SequenceMethod::kTriggered),
            SequenceMethodPersistence::kThroughTimeStep);
}

TEST(MulticlockEndPoint, MatchedConfinedToSequenceExpressions) {
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kMatched, SequenceMethodContext::kSequenceExpression,
      false));
  EXPECT_FALSE(IsSequenceMethodContextLegal(
      SequenceMethod::kMatched,
      SequenceMethodContext::kBooleanExpressionOutsideSequence, false));
}

constexpr const char* kEndingClockSequences =
    "  sequence s0; @(posedge clk0) a ##1 b; endsequence\n"
    "  sequence ms; @(posedge clk0) a ##1 @(posedge clk1) b; endsequence\n";

std::string EndingClockSource(const std::string& place,
                              const std::string& item) {
  std::string body = std::string(kEndingClockSequences) + item;
  std::string instance =
      "module m;\n  logic clk0, clk1, a, b, x;\n  w u(clk0, clk1, a, b, x);\n"
      "endmodule\n";
  if (place == "module") {
    return "module m;\n  logic clk0, clk1, a, b, x, y;\n" + body +
           "endmodule\n";
  }
  if (place == "interface" || place == "program") {
    return place + " w(input logic clk0, clk1, a, b, x);\n  logic y;\n" + body +
           "end" + place + "\n" + instance;
  }
  if (place == "checker") {
    return "checker w(clk0, clk1, a, b, x);\n  logic y;\n" + body +
           "endchecker\n" + instance;
  }
  if (place == "if generate") {
    return "module m;\n  logic clk0, clk1, a, b, x, y;\n  if (1) begin : g\n" +
           body + "  end\nendmodule\n";
  }
  if (place == "loop generate") {
    return "module m;\n  logic clk0, clk1, a, b, x, y;\n"
           "  for (genvar i = 0; i < 1; i++) begin : g\n" +
           body + "  end\nendmodule\n";
  }
  if (place == "package") {
    return "package pk;\n  logic clk0, clk1, a, b, x, y;\n" + body +
           "endpackage\nmodule m;\n  import pk::*;\nendmodule\n";
  }
  return "logic clk0, clk1, a, b, x, y;\n" + body + "module m;\nendmodule\n";
}

struct EndingClockForm {
  const char* forbidden;
  const char* allowed;
};

constexpr EndingClockForm kDeclaredEndingClockForms[] = {
    {"  sequence d; @(posedge clk1) x ##1 s0.triggered; endsequence\n",
     "  sequence d; @(posedge clk0) x ##1 s0.triggered; endsequence\n"},
    {"  property d; @(posedge clk1) x |-> s0.triggered; endproperty\n",
     "  property d; @(posedge clk0) x |-> s0.triggered; endproperty\n"},
    {"  sequence d; @(posedge clk0) x ##1 @(posedge clk1) s0.triggered; "
     "endsequence\n",
     "  sequence d; @(posedge clk1) x ##1 @(posedge clk0) s0.triggered; "
     "endsequence\n"},
    {"  property d; @(posedge clk0) x |=> @(posedge clk1) s0.triggered; "
     "endproperty\n",
     "  property d; @(posedge clk1) x |=> @(posedge clk0) s0.triggered; "
     "endproperty\n"},
    {"  sequence d; @(posedge clk0) x ##1 ms.triggered; endsequence\n",
     "  sequence d; @(posedge clk1) x ##1 ms.triggered; endsequence\n"},
    {"  property d; @(posedge clk0) x |-> ms.triggered; endproperty\n",
     "  property d; @(posedge clk1) x |-> ms.triggered; endproperty\n"},
    {"  sequence d; @(posedge clk1) x ##1 @(posedge clk0) ms.triggered; "
     "endsequence\n",
     "  sequence d; @(posedge clk0) x ##1 @(posedge clk1) ms.triggered; "
     "endsequence\n"},
    {"  property d; @(posedge clk1) x |=> @(posedge clk0) ms.triggered; "
     "endproperty\n",
     "  property d; @(posedge clk0) x |=> @(posedge clk1) ms.triggered; "
     "endproperty\n"}};

constexpr EndingClockForm kImplicationAssertionEndingClockForms[] = {
    {"  assert property (@(posedge clk1) x |-> s0.triggered);\n",
     "  assert property (@(posedge clk0) x |-> s0.triggered);\n"},
    {"  assume property (@(posedge clk1) x |-> s0.triggered);\n",
     "  assume property (@(posedge clk0) x |-> s0.triggered);\n"},
    {"  cover property (@(posedge clk1) x |-> s0.triggered);\n",
     "  cover property (@(posedge clk0) x |-> s0.triggered);\n"},
    {"  assert property (@(posedge clk0) x |-> ms.triggered);\n",
     "  assert property (@(posedge clk1) x |-> ms.triggered);\n"},
    {"  assume property (@(posedge clk0) x |=> ms.triggered);\n",
     "  assume property (@(posedge clk0) x |=> @(posedge clk1) "
     "ms.triggered);\n"},
    {"  cover property (@(posedge clk0) x |-> ms.triggered);\n",
     "  cover property (@(posedge clk1) x |-> ms.triggered);\n"}};

constexpr EndingClockForm kSequenceAssertionEndingClockForms[] = {
    {"  assert property (@(posedge clk1) x ##1 s0.triggered);\n",
     "  assert property (@(posedge clk0) x ##1 s0.triggered);\n"},
    {"  assume property (@(posedge clk1) s0.triggered);\n",
     "  assume property (@(posedge clk0) s0.triggered);\n"},
    {"  cover property (@(posedge clk1) x ##0 s0.triggered);\n",
     "  cover property (@(posedge clk0) x ##0 s0.triggered);\n"},
    {"  cover sequence (@(posedge clk1) x ##1 s0.triggered);\n",
     "  cover sequence (@(posedge clk0) x ##1 s0.triggered);\n"},
    {"  assert property (@(posedge clk0) ms.triggered);\n",
     "  assert property (@(posedge clk1) ms.triggered);\n"},
    {"  cover sequence (@(posedge clk0) x ##1 ms.triggered);\n",
     "  cover sequence (@(posedge clk1) x ##1 ms.triggered);\n"}};

constexpr EndingClockForm kProcedureEndingClockForms[] = {
    {"  always @(posedge clk1) y <= s0.triggered;\n",
     "  always @(posedge clk0) y <= s0.triggered;\n"},
    {"  always @(posedge clk0) y <= ms.triggered;\n",
     "  always @(posedge clk1) y <= ms.triggered;\n"}};

constexpr EndingClockForm kCheckerProcedureEndingClockForms[] = {
    {"  always_ff @(posedge clk1) y <= s0.triggered;\n",
     "  always_ff @(posedge clk0) y <= s0.triggered;\n"},
    {"  always_ff @(posedge clk0) y <= ms.triggered;\n",
     "  always_ff @(posedge clk1) y <= ms.triggered;\n"}};

template <typename Places, typename Forms>
void ExpectEndingClocksJudgedIn(const Places& places, const Forms& forms) {
  for (const char* name : places) {
    std::string place = name;
    for (const EndingClockForm& form : forms) {
      std::string forbidden = EndingClockSource(place, form.forbidden);
      std::string source_name =
          std::string(form.forbidden).find("ms.") == std::string::npos ? "s0"
                                                                       : "ms";
      {
        SCOPED_TRACE(forbidden);
        ElabFixture f;
        ElaborateSrc(forbidden, f);
        EXPECT_TRUE(ReportedError(
            f.diag.Diagnostics(),
            "the ending clock of '" + source_name +
                "' differs from the clock of the context its triggered "
                "stands in",
            LineHolding(forbidden, form.forbidden), "16.9.11"));
      }
      std::string allowed = EndingClockSource(place, form.allowed);
      SCOPED_TRACE(allowed);
      ElabFixture f;
      ElaborateSrc(allowed, f);
      EXPECT_EQ(f.diag.ErrorCount(), 0u);
    }
  }
}

constexpr const char* kEndingClockDesignUnits[] = {"module", "interface",
                                                   "program", "checker"};

TEST(TriggeredEndingClock, EachDeclaredDestinationIsJudgedInEachDesignUnit) {
  ExpectEndingClocksJudgedIn(kEndingClockDesignUnits,
                             kDeclaredEndingClockForms);
}

TEST(TriggeredEndingClock, AnImplicationInAnAssertionIsJudgedInEachDesignUnit) {
  ExpectEndingClocksJudgedIn(kEndingClockDesignUnits,
                             kImplicationAssertionEndingClockForms);
}

TEST(TriggeredEndingClock, AProcedureIsJudgedInAModuleAnInterfaceAndAChecker) {
  ExpectEndingClocksJudgedIn(
      std::initializer_list<const char*>{"module", "interface"},
      kProcedureEndingClockForms);
  ExpectEndingClocksJudgedIn(std::initializer_list<const char*>{"checker"},
                             kCheckerProcedureEndingClockForms);
}

TEST(TriggeredEndingClock,
     DISABLED_ASequenceAssertionIsJudgedInEachDesignUnit) {
  ExpectEndingClocksJudgedIn(kEndingClockDesignUnits,
                             kSequenceAssertionEndingClockForms);
}

TEST(TriggeredEndingClock, DISABLED_EachFormIsJudgedInAGenerateBlock) {
  constexpr const char* kGenerateBlocks[] = {"if generate", "loop generate"};
  ExpectEndingClocksJudgedIn(kGenerateBlocks, kDeclaredEndingClockForms);
  ExpectEndingClocksJudgedIn(kGenerateBlocks,
                             kImplicationAssertionEndingClockForms);
  ExpectEndingClocksJudgedIn(kGenerateBlocks, kProcedureEndingClockForms);
}

TEST(TriggeredEndingClock,
     DISABLED_EachDeclarationIsJudgedInAPackageAndTheCompilationUnit) {
  ExpectEndingClocksJudgedIn(
      std::initializer_list<const char*>{"package", "unit"},
      kDeclaredEndingClockForms);
}

constexpr const char* kLocalSourceModule =
    "module m;\n"
    "  logic clk, sysclk, a, b;\n"
    "  int data;\n"
    "  sequence src(lv); @(posedge clk) (a, lv = data) ##1 b; endsequence\n"
    "  sequence srci(local input int lv); @(posedge clk) a ##1 (b, lv = "
    "data); endsequence\n"
    "  sequence srcio(local inout int lv); @(posedge clk) a ##1 (b, lv = "
    "data); endsequence\n"
    "  sequence srco(local output int lv); @(posedge clk) (a, lv = data) ##1 "
    "b; endsequence\n";

std::string LocalSourceModule(const std::string& items) {
  return kLocalSourceModule + items + "endmodule\n";
}

TEST(MatchedLocalFlow, AnInputOrInoutLocalFormalUnderMatchedIsReported) {
  for (const char* instance : {"srci", "srcio"}) {
    std::string src = LocalSourceModule(
        "  sequence d; int v; @(posedge sysclk) (1, v = 0) ##0 " +
        std::string(instance) + "(v).matched; endsequence\n");
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "matched may not be applied to an instance of '" +
            std::string(instance) +
            "', which has an input or inout local variable formal argument",
        LineHolding(src, "sequence d;"), "16.8.2"));
  }
  std::string src = LocalSourceModule(
      "  sequence d; int v; @(posedge sysclk) srco(v).matched ##0 (v == 1); "
      "endsequence\n");
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(MatchedLocalFlow, ALocalInsideAnActualOfMatchedIsReported) {
  std::string src = LocalSourceModule(
      "  sequence d; int v; @(posedge sysclk) (1, v = 0) ##0 src(v + "
      "1).matched; endsequence\n");
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a local variable passed to an instance that "
                            "matched is applied to shall be an entire actual "
                            "argument",
                            LineHolding(src, "sequence d;"), "16.13.5"));
  std::string whole = LocalSourceModule(
      "  sequence d; int v; @(posedge sysclk) src(v).matched ##0 (v == 1); "
      "endsequence\n");
  ElabFixture g;
  ElaborateSrc(whole, g);
  EXPECT_EQ(g.diag.ErrorCount(), 0u);
}

TEST(MatchedLocalFlow, DISABLED_APropertysWholeBodyMayBeAMatchedInstance) {
  std::string src = LocalSourceModule(
      "  property d; int v; @(posedge sysclk) src(v).matched; endproperty\n"
      "  cover property (d);\n");
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(MatchedLocalFlow,
     DISABLED_ANonMaximalMatchedReportsOnlyTheLaterReadOfTheLocal) {
  for (const char* application :
       {"!src(v).matched", "~src(v).matched", "src(v).matched && a"}) {
    std::string src = LocalSourceModule(
        "  sequence d; int v;\n"
        "    @(posedge sysclk) " +
        std::string(application) +
        "\n"
        "    ##0 (v == 1); endsequence\n");
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "the local variable 'v' is referenced at a point where it is "
        "unassigned",
        LineHolding(src, "##0 (v == 1)"), "16.10"));
    EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(),
                             LineHolding(src, "@(posedge sysclk)")));
  }
}

}  // namespace
