#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "elaborator/inferred_clock_disable.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(InferredClockDisable, ClassifiesTheTwoSystemFunctions) {
  EXPECT_EQ(ClassifyInferredFunction("$inferred_clock"),
            InferredFunction::kClock);
  EXPECT_EQ(ClassifyInferredFunction("$inferred_disable"),
            InferredFunction::kDisable);
  EXPECT_EQ(ClassifyInferredFunction("$rose"), InferredFunction::kNone);
  EXPECT_EQ(ClassifyInferredFunction("$inferred"), InferredFunction::kNone);
}

TEST(InferredClockDisable, BothAreElaborationTimeFunctions) {
  EXPECT_TRUE(IsElaborationTimeInferredFunction(InferredFunction::kClock));
  EXPECT_TRUE(IsElaborationTimeInferredFunction(InferredFunction::kDisable));
  EXPECT_FALSE(IsElaborationTimeInferredFunction(InferredFunction::kNone));
}

TEST(InferredClockDisable, InferredClockIsResolvedEventExpression) {
  auto r = ResolveInferredClock("posedge clk");
  EXPECT_FALSE(r.is_error);
  EXPECT_EQ(r.event, "posedge clk");
}

TEST(InferredClockDisable, InferredClockErrorsWhenNoEventInScope) {
  auto r = ResolveInferredClock("");
  EXPECT_TRUE(r.is_error);
  EXPECT_TRUE(r.event.empty());
}

TEST(InferredClockDisable, InferredDisableUsesDefaultDisableInScope) {
  EXPECT_EQ(ResolveInferredDisable(true, "rst"), "rst");
}

TEST(InferredClockDisable, InferredDisableIsFalseOutsideAnyScope) {
  EXPECT_EQ(ResolveInferredDisable(false, "ignored"), "1'b0");
}

TEST(InferredClockDisable, LegalOnlyAsEntireFormalDefaultOfAssertionDecl) {
  EXPECT_TRUE(InferredFunctionPlacementIsLegal(
      FormalArgumentOwner::kProperty,
      DefaultValuePosition::kEntireDefaultValue));
  EXPECT_TRUE(InferredFunctionPlacementIsLegal(
      FormalArgumentOwner::kSequence,
      DefaultValuePosition::kEntireDefaultValue));
  EXPECT_TRUE(InferredFunctionPlacementIsLegal(
      FormalArgumentOwner::kChecker,
      DefaultValuePosition::kEntireDefaultValue));
}

TEST(InferredClockDisable, IllegalAsPartialDefaultOrWrongOwner) {
  EXPECT_FALSE(InferredFunctionPlacementIsLegal(
      FormalArgumentOwner::kProperty,
      DefaultValuePosition::kPartOfDefaultValue));
  EXPECT_FALSE(InferredFunctionPlacementIsLegal(
      FormalArgumentOwner::kProperty, DefaultValuePosition::kNotADefaultValue));
  EXPECT_FALSE(InferredFunctionPlacementIsLegal(
      FormalArgumentOwner::kOther, DefaultValuePosition::kEntireDefaultValue));
}

TEST(InferredClockDisable, ReplacementSourceFollowsInstantiationContext) {
  EXPECT_EQ(InferredClockReplacementSource(
                InstantiationContext::kTopLevelAssertionInstance),
            InferredClockReplacement::kAssertionStatementLocation);
  EXPECT_EQ(InferredClockReplacementSource(
                InstantiationContext::kNestedPropertyInstance),
            InferredClockReplacement::kClockFlowUpToInstance);
  EXPECT_EQ(
      InferredClockReplacementSource(InstantiationContext::kCheckerInstance),
      InferredClockReplacement::kCheckerInstanceLocation);
}

TEST(InferredClockDisable, AnInferredClockResolvingToNothingIsReported) {
  const char* const kReport =
      "$inferred_clock, the default of the formal 'clk' of 'p', has no "
      "resolved clocking event at this instance";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit a;\n"
      "  property p(clk = $inferred_clock);\n"
      "    @clk a;\n"
      "  endproperty\n"
      "  a1: assert property (p);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 6, "16.14.7"));
  ElabFixture g;
  ElaborateSrc(
      "module m;\n"
      "  bit a, clk;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  property p(clk = $inferred_clock);\n"
      "    @clk a;\n"
      "  endproperty\n"
      "  a1: assert property (p);\n"
      "endmodule\n",
      g);
  EXPECT_FALSE(ReportedError(g.diag.Diagnostics(), kReport, 7, "16.14.7"));
}

constexpr const char* kMisplaced =
    "an inferred clocking or disable function must be the entire default "
    "value of a formal argument";

constexpr const char* kTypedClock =
    "$inferred_clock default requires an untyped or event formal argument";

constexpr const char* kPlaces[] = {"module",  "interface", "program", "package",
                                   "checker", "generate",  "unit"};

std::string InPlace(const std::string& place, const std::string& items) {
  if (place == "module") return "module top;\n" + items + "endmodule\n";
  if (place == "generate") {
    return "module top;\n  if (1) begin : g\n" + items + "  end\nendmodule\n";
  }
  if (place == "unit") return items + "module top; endmodule\n";
  if (place == "package") {
    return "package pk;\n" + items +
           "endpackage\nmodule top;\n  import pk::*;\nendmodule\n";
  }
  return place + " w;\n" + items + "end" + place +
         "\nmodule top;\n  w u();\nendmodule\n";
}

void ExpectNoErrors(const std::string& src) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

void ExpectReportedOnce(const std::string& src, const char* message,
                        const std::string& marker) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(src, f);
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                            LineHolding(src, marker), "16.14.7"));
}

std::string Misplaced(const std::string& items) {
  return "module m;\n"
         "  logic clk = 0, a = 1, rst = 0, x;\n"
         "  default clocking @(posedge clk); endclocking\n"
         "  default disable iff rst;\n" +
         items + "endmodule\n";
}

void ExpectEachMisplacedCallReported(const std::string& src) {
  for (std::string fn : {"$inferred_clock", "$inferred_disable"}) {
    std::string named = src;
    named.replace(named.find("$F"), 2, fn);
    ExpectReportedOnce(named, kMisplaced, fn);
  }
}

constexpr const char* kWholeDefaults =
    "  property p(c = $inferred_clock, d = $inferred_disable);\n"
    "    @(c) disable iff (d) 1'b1;\n"
    "  endproperty\n"
    "  sequence s(c = $inferred_clock, d = $inferred_disable);\n"
    "    @(c) !d;\n"
    "  endsequence\n"
    "  checker k(c = $inferred_clock, d = $inferred_disable);\n"
    "  endchecker\n";

TEST(InferredClockDisable,
     AWholeInferredDefaultIsAcceptedWhereverItsDeclarationStands) {
  for (const char* place : kPlaces)
    ExpectNoErrors(InPlace(place, kWholeDefaults));
}

TEST(InferredClockDisable,
     DISABLED_AnInferredCallWithEmptyParenthesesIsAWholeDefault) {
  std::string items = kWholeDefaults;
  for (std::string fn : {"$inferred_clock", "$inferred_disable"}) {
    for (size_t at = items.find(fn); at != std::string::npos;
         at = items.find(fn, at + fn.size() + 2)) {
      items.insert(at + fn.size(), "()");
    }
  }
  ExpectNoErrors(InPlace("module", items));
}

TEST(InferredClockDisable,
     DISABLED_AnInferredCallAsALaterOperandOfADefaultIsReported) {
  for (const char* items :
       {"  property p(e = a || $F); e; endproperty\n",
        "  sequence s(e = a || $F); e; endsequence\n",
        "  checker k(logic v, untyped e = a || $F); endchecker\n",
        "  checker k(logic v, untyped e = a || $F); endchecker\n"
        "  k u(a);\n"}) {
    ExpectEachMisplacedCallReported(Misplaced(items));
  }
}

TEST(InferredClockDisable,
     DISABLED_AnInferredCallDefaultingALetFunctionOrTaskFormalIsReported) {
  for (const char* items :
       {"  let l(y = $F) = y;\n  a1: assert property (l());\n",
        "  function automatic bit f(bit y = $F); return y; endfunction\n",
        "  class c;\n    function bit f(bit y = $F); return y; endfunction\n"
        "  endclass\n",
        "  task automatic tk(bit y = $F); endtask\n"}) {
    ExpectEachMisplacedCallReported(Misplaced(items));
  }
  ExpectEachMisplacedCallReported(
      "package pk;\n"
      "  function automatic bit f(bit y = $F); return y; endfunction\n"
      "endpackage\n"
      "module m; endmodule\n");
}

TEST(InferredClockDisable,
     DISABLED_AnInferredCallAsAnActualArgumentIsReported) {
  for (const char* items : {"  property q(e); @(posedge clk) e; endproperty\n"
                            "  a1: assert property (q($F));\n",
                            "  sequence sq(e); e; endsequence\n"
                            "  a1: assert property (sq($F));\n",
                            "  checker k(logic v, untyped e); endchecker\n"
                            "  k u(a, $F);\n"}) {
    ExpectEachMisplacedCallReported(Misplaced(items));
  }
}

TEST(InferredClockDisable,
     DISABLED_AnInferredCallInADeclarationBodyIsReported) {
  for (const char* items :
       {"  property r; @($F) a; endproperty\n",
        "  property r; disable iff ($F) a; endproperty\n",
        "  sequence q; @($F) a; endsequence\n",
        "  checker k(logic v);\n    a1: assert property (@($F) v);\n"
        "  endchecker\n  k u(a);\n",
        "  checker k(logic v);\n"
        "    a1: assert property (disable iff ($F) @(posedge clk) v);\n"
        "  endchecker\n  k u(a);\n"}) {
    ExpectEachMisplacedCallReported(Misplaced(items));
  }
}

TEST(InferredClockDisable,
     DISABLED_AnInferredCallInAnAssertionOrOrdinaryExpressionIsReported) {
  for (const char* items : {"  a1: assert property (@($F) a);\n",
                            "  a1: assert property (disable iff ($F) a);\n",
                            "  assign x = $F;\n", "  initial x = $F;\n"}) {
    ExpectEachMisplacedCallReported(Misplaced(items));
  }
}

TEST(InferredClockDisable,
     AnInferredClockDefaultOnACheckerFormalWithoutADataTypeIsAccepted) {
  for (const char* formals :
       {"e = $inferred_clock", "logic v, untyped e = $inferred_clock",
        "event v, e = $inferred_clock",
        "logic v, input event e = $inferred_clock"}) {
    ExpectNoErrors(InPlace("module", "  checker k(" + std::string(formals) +
                                         ");\n  endchecker\n"));
  }
}

TEST(InferredClockDisable,
     DISABLED_AnInferredClockDefaultOnATypedCheckerFormalIsRejected) {
  for (const char* formals :
       {"event v, logic e", "event v, bit e", "event v, int e",
        "event v, my_t e", "event v, sequence e", "event v, property e",
        "logic v, e", "event v, [3:0] e", "event v, signed e"}) {
    std::string src =
        "module m;\n"
        "  typedef logic [1:0] my_t;\n"
        "  checker k(" +
        std::string(formals) +
        " = $inferred_clock);\n"
        "  endchecker\n"
        "endmodule\n";
    ExpectReportedOnce(src, kTypedClock, "checker k");
  }
}

TEST(
    InferredClockDisable,
    DISABLED_AnInferredClockDefaultOnATypedCheckerFormalIsRejectedWhereverDeclared) {
  for (const char* place : kPlaces) {
    ExpectReportedOnce(InPlace(place,
                               "  checker k(logic e = $inferred_clock);\n"
                               "  endchecker\n"),
                       kTypedClock, "checker k");
  }
}

TEST(InferredClockDisable,
     AnInferredClockDefaultOnATypedFormalIsRejectedWhereverDeclared) {
  for (const char* place : kPlaces) {
    for (const char* decl :
         {"  property p(logic e = $inferred_clock); 1'b1; endproperty\n",
          "  sequence s(logic e = $inferred_clock); 1'b1; endsequence\n"}) {
      ExpectReportedOnce(InPlace(place, decl), kTypedClock, "logic e");
    }
  }
}

TEST(InferredClockDisable,
     AnInferredClockResolvingToNothingIsReportedForASequence) {
  ElabFixture f;
  std::string src =
      "module m;\n"
      "  bit a;\n"
      "  sequence s(clk = $inferred_clock);\n"
      "    @clk a;\n"
      "  endsequence\n"
      "  a1: assert property (s);\n"
      "endmodule\n";
  ElaborateSrcAllowingParseErrors(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$inferred_clock, the default of the formal 'clk' "
                            "of 's', has no resolved clocking event at this "
                            "instance",
                            6, "16.14.7"));
}

TEST(InferredClockDisable,
     DISABLED_AnInferredClockResolvingToNothingIsReportedForAChecker) {
  ElabFixture f;
  std::string src =
      "module m;\n"
      "  bit a;\n"
      "  checker k(logic v, event clk = $inferred_clock);\n"
      "    a1: assert property (@clk v);\n"
      "  endchecker\n"
      "  k u(a);\n"
      "endmodule\n";
  ElaborateSrcAllowingParseErrors(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$inferred_clock, the default of the formal 'clk' "
                            "of 'k', has no resolved clocking event at this "
                            "instance",
                            6, "16.14.7"));
}

}  // namespace
