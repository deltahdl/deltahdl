#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>

#include "elaborator/abort_property.h"
#include "elaborator/sampled_value.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AbortProperty, RecognizesEveryAbortOperator) {
  AbortOperator op{};
  EXPECT_TRUE(ClassifyAbortOperator("accept_on", op));
  EXPECT_EQ(op, AbortOperator::kAcceptOn);
  EXPECT_TRUE(ClassifyAbortOperator("reject_on", op));
  EXPECT_EQ(op, AbortOperator::kRejectOn);
  EXPECT_TRUE(ClassifyAbortOperator("sync_accept_on", op));
  EXPECT_EQ(op, AbortOperator::kSyncAcceptOn);
  EXPECT_TRUE(ClassifyAbortOperator("sync_reject_on", op));
  EXPECT_EQ(op, AbortOperator::kSyncRejectOn);
}

TEST(AbortProperty, RejectsNonAbortKeywords) {
  EXPECT_FALSE(IsAbortOperator("disable"));
  EXPECT_FALSE(IsAbortOperator("accept"));
  EXPECT_FALSE(IsAbortOperator("sync_on"));
}

TEST(AbortProperty, SyncFormsAreSynchronousAbortProperties) {
  EXPECT_FALSE(IsSynchronousAbort(AbortOperator::kAcceptOn));
  EXPECT_FALSE(IsSynchronousAbort(AbortOperator::kRejectOn));
  EXPECT_TRUE(IsSynchronousAbort(AbortOperator::kSyncAcceptOn));
  EXPECT_TRUE(IsSynchronousAbort(AbortOperator::kSyncRejectOn));
}

TEST(AbortProperty, AcceptFormsForceTrueAndRejectFormsForceFalse) {
  EXPECT_TRUE(AbortConditionForcesTrue(AbortOperator::kAcceptOn));
  EXPECT_TRUE(AbortConditionForcesTrue(AbortOperator::kSyncAcceptOn));
  EXPECT_FALSE(AbortConditionForcesTrue(AbortOperator::kRejectOn));
  EXPECT_FALSE(AbortConditionForcesTrue(AbortOperator::kSyncRejectOn));
}

TEST(AbortProperty, NestingOfAbortOperatorsIsAllowed) {
  EXPECT_TRUE(AbortOperatorsMayNest());
}

TEST(AbortProperty, AbortConditionForbidsLocalVariablesTriggeredAndMatched) {
  EXPECT_FALSE(AbortConditionAllowsLocalVariableReference());
  EXPECT_FALSE(AbortConditionAllowsTriggeredMethod());
  EXPECT_FALSE(AbortConditionAllowsMatchedMethod());

  EXPECT_TRUE(AbortConditionContentIsLegal(false, false, false));
  EXPECT_FALSE(AbortConditionContentIsLegal(true, false, false));
  EXPECT_FALSE(AbortConditionContentIsLegal(false, true, false));
  EXPECT_FALSE(AbortConditionContentIsLegal(false, false, true));
}

TEST(AbortProperty, NonSampledSampledValueFunctionsRequireExplicitClock) {
  EXPECT_FALSE(AbortConditionSampledValueRequiresExplicitClock(
      SampledValueFunction::kSampled));
  EXPECT_TRUE(AbortConditionSampledValueRequiresExplicitClock(
      SampledValueFunction::kRose));
  EXPECT_TRUE(AbortConditionSampledValueRequiresExplicitClock(
      SampledValueFunction::kPast));

  EXPECT_TRUE(AbortConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kSampled, false));
  EXPECT_TRUE(AbortConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kSampled, true));
  EXPECT_FALSE(AbortConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kChanged, false));
  EXPECT_TRUE(AbortConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kChanged, true));
}

TEST(AbortProperty, SampledValueFunctionsArePermittedInAbortConditions) {
  for (SampledValueFunction fn :
       {SampledValueFunction::kSampled, SampledValueFunction::kRose,
        SampledValueFunction::kFell, SampledValueFunction::kStable,
        SampledValueFunction::kChanged, SampledValueFunction::kPast}) {
    const bool kClockExplicit =
        AbortConditionSampledValueRequiresExplicitClock(fn);
    EXPECT_TRUE(
        AbortConditionSampledValueClockIsWellFormed(fn, kClockExplicit));
  }
}

TEST(AbortProperty, ClassificationRejectsCaseVariantsAndEmptyKeyword) {
  AbortOperator op{};
  EXPECT_FALSE(ClassifyAbortOperator("", op));
  EXPECT_FALSE(IsAbortOperator("Accept_On"));
  EXPECT_FALSE(IsAbortOperator("SYNC_REJECT_ON"));
  EXPECT_FALSE(IsAbortOperator("accept_on "));
  EXPECT_FALSE(IsAbortOperator("reject"));
}

TEST(AbortProperty, AbortConditionRejectsAllForbiddenReferencesAtOnce) {
  EXPECT_FALSE(AbortConditionContentIsLegal(true, true, true));
}

TEST(AbortConditionRules, ALocalOrSequenceMethodIsReported) {
  const char* const kReport =
      "an abort condition may not reference a local variable or the sequence "
      "methods triggered and matched";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  property p;\n"
      "    int v;\n"
      "    @(posedge clk) (1, v = b) |-> accept_on (v == 1) a;\n"
      "  endproperty\n"
      "  a1: assert property (@(posedge clk) reject_on (s.triggered) a);\n"
      "  a2: assert property (@(posedge clk) reject_on (c) a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 8, "16.12.14"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 10, "16.12.14"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 11, "16.12.14"));
}

TEST(AbortConditionRules, AnUnclockedSampledValueCallIsReported) {
  const char* const kReport =
      "$rose in an abort condition shall have its clocking event specified "
      "explicitly";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, c;\n"
      "  a1: assert property (@(posedge clk) accept_on ($rose(c)) a);\n"
      "  a2: assert property (@(posedge clk)\n"
      "    accept_on ($rose(c, @(posedge clk))) a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 3, "16.12.14"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 5, "16.12.14"));
}

constexpr const char* kAbortReport =
    "an abort condition may not reference a local variable or the sequence "
    "methods triggered and matched";

constexpr const char* kAbortOperators[] = {"accept_on", "reject_on",
                                           "sync_accept_on", "sync_reject_on"};

constexpr int kAbortLine = 4;

std::string AbortPropertyLine(const std::string& place, const std::string& op,
                              const std::string& condition) {
  std::string clock = place == "clocking" ? "" : "@(posedge clk) ";
  return "  property p(local input int w = 1, sequence q = s); int v; " +
         clock + "(1, v = b) |-> " + op + " (" + condition +
         ") a; endproperty\n";
}

std::string AbortIn(const std::string& place, const std::string& property) {
  const std::string kHead =
      "  bit clk, a, b, c;\n"
      "  sequence s; @(posedge clk) a ##1 b; endsequence";
  const std::string kUse = "  a1: assert property (p);\n";
  if (place == "interface" || place == "program" || place == "checker") {
    std::string top =
        place == "program" ? "" : "module top; m u(); endmodule\n";
    return place + " m;\n" + kHead + "\n" + property + kUse + "end" + place +
           "\n" + top;
  }
  if (place == "generate") {
    return "module m;\n" + kHead + " if (1) begin : g\n" + property + kUse +
           "  end\nendmodule\n";
  }
  if (place == "clocking") {
    return "module m;\n" + kHead + " clocking cb @(posedge clk);\n" + property +
           "  endclocking\nendmodule\n";
  }
  if (place == "package") {
    return "package pk;\n" + kHead + "\n" + property +
           "endpackage\nmodule m;\n  import pk::*;\n" + kUse + "endmodule\n";
  }
  if (place == "unit") {
    return "\n" + kHead + "\n" + property + "module m;\n" + kUse +
           "endmodule\n";
  }
  return "module m;\n" + kHead + "\n" + property + kUse + "endmodule\n";
}

constexpr const char* kForbiddenConditions[] = {
    "v",           "v == 1",    "w",           "s.triggered", "s.matched",
    "q.triggered", "q.matched", "$sampled(v)", "c || v"};

constexpr const char* kAllowedConditions[] = {"c", "$sampled(c)", "c == 1",
                                              "!c"};

constexpr const char* kReportingPlaces[] = {"module", "interface", "program",
                                            "checker"};

constexpr const char* kSilentPlaces[] = {"package", "generate", "clocking",
                                         "unit"};

bool AbortReported(const std::string& src, int line) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return ReportedError(f.diag.Diagnostics(), kAbortReport, line, "16.12.14");
}

template <size_t Places>
void ExpectAbortConditions(const char* const (&places)[Places],
                           const char* const* conditions, size_t count,
                           bool reported) {
  for (const char* place : places) {
    for (const char* op : kAbortOperators) {
      for (size_t i = 0; i < count; ++i) {
        SCOPED_TRACE(std::string(place) + " " + op + " (" + conditions[i] +
                     ")");
        EXPECT_EQ(AbortReported(AbortIn(place, AbortPropertyLine(
                                                   place, op, conditions[i])),
                                kAbortLine),
                  reported);
      }
    }
  }
}

TEST(AbortConditionRules, AForbiddenReferenceIsReportedInEachOperatorAndPlace) {
  ExpectAbortConditions(kReportingPlaces, kForbiddenConditions,
                        std::size(kForbiddenConditions), true);
}

TEST(AbortConditionRules,
     DISABLED_AForbiddenReferenceIsReportedInAPackageGenerateClockingOrUnit) {
  ExpectAbortConditions(kSilentPlaces, kForbiddenConditions,
                        std::size(kForbiddenConditions), true);
}

TEST(AbortConditionRules, AnAllowedConditionIsAcceptedInEachOperatorAndPlace) {
  ExpectAbortConditions(kReportingPlaces, kAllowedConditions,
                        std::size(kAllowedConditions), false);
  ExpectAbortConditions(kSilentPlaces, kAllowedConditions,
                        std::size(kAllowedConditions), false);
}

TEST(AbortConditionRules, AForbiddenReferenceInANestedAbortIsReported) {
  for (const char* outer : kAbortOperators) {
    for (const char* inner : kAbortOperators) {
      SCOPED_TRACE(std::string(outer) + " " + inner);
      std::string body = std::string(outer) + " (c) " + inner + " (v) a";
      EXPECT_TRUE(AbortReported(
          AbortIn("module",
                  "  property p; int v; @(posedge clk) (1, v = b) "
                  "|-> " +
                      body + "; endproperty\n"),
          kAbortLine));
      body = std::string(outer) + " (v) " + inner + " (c) a";
      EXPECT_TRUE(AbortReported(
          AbortIn("module",
                  "  property p; int v; @(posedge clk) (1, v = b) "
                  "|-> " +
                      body + "; endproperty\n"),
          kAbortLine));
    }
  }
  EXPECT_FALSE(
      AbortReported(AbortIn("module",
                            "  property p; @(posedge clk) accept_on (c) "
                            "reject_on (b) a; endproperty\n"),
                    kAbortLine));
}

TEST(AbortConditionRules, AForbiddenReferenceInARecursivePropertyIsReported) {
  for (const char* op : kAbortOperators) {
    SCOPED_TRACE(op);
    EXPECT_TRUE(AbortReported(
        AbortIn("module", std::string("  property p(local input int w = 1); "
                                      "@(posedge clk) ") +
                              op + " (w) (a and nexttime p(w)); endproperty\n"),
        kAbortLine));
    EXPECT_FALSE(AbortReported(
        AbortIn("module", std::string("  property p(int w = 1); "
                                      "@(posedge clk) ") +
                              op + " (c) (a and nexttime p(w)); endproperty\n"),
        kAbortLine));
  }
}

std::string ProceduralAbort(const std::string& condition) {
  return "module m;\n"
         "  bit clk, a, b, c;\n"
         "  sequence s; @(posedge clk) a ##1 b; endsequence\n"
         "  always @(posedge clk) a1: assert property (reject_on (" +
         condition + ") a);\nendmodule\n";
}

TEST(AbortConditionRules, ASequenceMethodInAProceduralAssertionIsReported) {
  EXPECT_TRUE(AbortReported(ProceduralAbort("s.triggered"), kAbortLine));
  EXPECT_TRUE(AbortReported(ProceduralAbort("s.matched"), kAbortLine));
  EXPECT_FALSE(AbortReported(ProceduralAbort("c"), kAbortLine));
}

std::string FormalAbort(const std::string& op, const std::string& actual) {
  return "module m;\n"
         "  bit clk, a, b, c;\n"
         "  sequence s; @(posedge clk) a ##1 b; endsequence\n"
         "  property pf(x); @(posedge clk) " +
         op +
         " (x) a; endproperty\n"
         "  property po; int v; @(posedge clk) (1, v = b) |-> pf(" +
         (actual == "v" ? "v" : "c") +
         "); endproperty\n"
         "  a1: assert property (" +
         (actual == "v" ? std::string("po") : "pf(" + actual + ")") +
         ");\nendmodule\n";
}

TEST(AbortConditionRules,
     DISABLED_AForbiddenActualOfAFormalInAnAbortConditionIsReported) {
  for (const char* op : kAbortOperators) {
    SCOPED_TRACE(op);
    EXPECT_TRUE(AbortReported(FormalAbort(op, "s.triggered"), 6));
    EXPECT_TRUE(AbortReported(FormalAbort(op, "s.matched"), 6));
    EXPECT_TRUE(AbortReported(FormalAbort(op, "v"), 5));
  }
}

TEST(AbortConditionRules, APlainActualOfAFormalInAnAbortConditionIsAccepted) {
  for (const char* op : kAbortOperators) {
    SCOPED_TRACE(op);
    for (const char* actual : {"c", "$sampled(c)", "!c"}) {
      std::string src = FormalAbort(op, actual);
      EXPECT_FALSE(AbortReported(src, 4));
      EXPECT_FALSE(AbortReported(src, 5));
      EXPECT_FALSE(AbortReported(src, 6));
    }
  }
}

constexpr const char* kClockSuffix =
    " in an abort condition shall have its clocking event specified "
    "explicitly";

std::string ClockedAbort(const std::string& op, const std::string& condition) {
  return "module m;\n"
         "  bit clk, a, c;\n"
         "  a1: assert property (@(posedge clk) " +
         op + " (" + condition + ") a);\nendmodule\n";
}

TEST(AbortConditionRules, AnUnclockedSampledValueCallIsReportedInEachOperator) {
  for (const char* op : kAbortOperators) {
    for (const char* function :
         {"$rose", "$fell", "$stable", "$changed", "$past"}) {
      SCOPED_TRACE(std::string(op) + " " + function);
      ElabFixture f;
      ElaborateSrc(ClockedAbort(op, std::string(function) + "(c)"), f);
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                                std::string(function) + kClockSuffix, 3,
                                "16.12.14"));
    }
  }
}

TEST(AbortConditionRules, AClockedOrSampledCallIsAcceptedInEachOperator) {
  for (const char* op : kAbortOperators) {
    for (const char* condition :
         {"$rose(c, @(posedge clk))", "$fell(c, @(posedge clk))",
          "$stable(c, @(posedge clk))", "$changed(c, @(posedge clk))",
          "$past(c, 1, 1, @(posedge clk))", "$sampled(c)"}) {
      SCOPED_TRACE(std::string(op) + " " + condition);
      ElabFixture f;
      ElaborateSrc(ClockedAbort(op, condition), f);
      EXPECT_FALSE(f.diag.HasErrors());
    }
  }
}

}  // namespace
