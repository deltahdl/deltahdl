#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ValueChangeArguments, AClockingEventFollowsTheExpressionInAnAssertion) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $fell(a, @clk));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $stable(a, @clk));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $changed(a, @clk));\n"
              "endmodule\n"));
}

TEST(ValueChangeArguments, AnEmptyClockingEventSlotIsAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $rose(a, ));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $fell(a, ));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $stable(a, ));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $changed(a, ));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  initial x = $rose(a, );\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  initial x = $fell(a, );\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  initial x = $stable(a, );\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  initial x = $changed(a, );\n"
              "endmodule\n"));
}

TEST(ValueChangeArguments, DISABLED_RoseWithNoArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $rose());\n"
            "endmodule\n")
          .diags,
      "$rose takes one expression and an optional clocking event", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $rose();\n"
            "endmodule\n")
          .diags,
      "$rose takes one expression and an optional clocking event", 3, "20.12"));
}

TEST(ValueChangeArguments,
     DISABLED_RoseWithAnEmptyFirstArgumentIsReportedInAnAssertion) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $rose(, @clk));\n"
            "endmodule\n")
          .diags,
      "$rose takes one expression and an optional clocking event", 3, "20.12"));
}

TEST(ValueChangeArguments,
     DISABLED_RoseWithAnExpressionAsItsSecondArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $rose(a, b));\n"
            "endmodule\n")
          .diags,
      "$rose takes one expression and an optional clocking event", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $rose(a, b);\n"
            "endmodule\n")
          .diags,
      "$rose takes one expression and an optional clocking event", 3, "20.12"));
}

TEST(ValueChangeArguments, DISABLED_RoseWithAThirdArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $rose(a, @clk, b));\n"
            "endmodule\n")
          .diags,
      "$rose takes one expression and an optional clocking event", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $rose(a,,));\n"
            "endmodule\n")
          .diags,
      "$rose takes one expression and an optional clocking event", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $rose(a, @clk, b);\n"
            "endmodule\n")
          .diags,
      "$rose takes one expression and an optional clocking event", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $rose(a,,);\n"
            "endmodule\n")
          .diags,
      "$rose takes one expression and an optional clocking event", 3, "20.12"));
}

TEST(ValueChangeArguments, DISABLED_RoseWithADataTypeArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $rose(int));\n"
            "endmodule\n")
          .diags,
      "$rose takes one expression and an optional clocking event", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $rose(int);\n"
            "endmodule\n")
          .diags,
      "$rose takes one expression and an optional clocking event", 3, "20.12"));
}

TEST(ValueChangeArguments, DISABLED_FellWithNoArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $fell());\n"
            "endmodule\n")
          .diags,
      "$fell takes one expression and an optional clocking event", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $fell();\n"
            "endmodule\n")
          .diags,
      "$fell takes one expression and an optional clocking event", 3, "20.12"));
}

TEST(ValueChangeArguments,
     DISABLED_FellWithAnEmptyFirstArgumentIsReportedInAnAssertion) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $fell(, @clk));\n"
            "endmodule\n")
          .diags,
      "$fell takes one expression and an optional clocking event", 3, "20.12"));
}

TEST(ValueChangeArguments,
     DISABLED_FellWithAnExpressionAsItsSecondArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $fell(a, b));\n"
            "endmodule\n")
          .diags,
      "$fell takes one expression and an optional clocking event", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $fell(a, b);\n"
            "endmodule\n")
          .diags,
      "$fell takes one expression and an optional clocking event", 3, "20.12"));
}

TEST(ValueChangeArguments, DISABLED_FellWithAThirdArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $fell(a, @clk, b));\n"
            "endmodule\n")
          .diags,
      "$fell takes one expression and an optional clocking event", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $fell(a,,));\n"
            "endmodule\n")
          .diags,
      "$fell takes one expression and an optional clocking event", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $fell(a, @clk, b);\n"
            "endmodule\n")
          .diags,
      "$fell takes one expression and an optional clocking event", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $fell(a,,);\n"
            "endmodule\n")
          .diags,
      "$fell takes one expression and an optional clocking event", 3, "20.12"));
}

TEST(ValueChangeArguments, DISABLED_FellWithADataTypeArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $fell(int));\n"
            "endmodule\n")
          .diags,
      "$fell takes one expression and an optional clocking event", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $fell(int);\n"
            "endmodule\n")
          .diags,
      "$fell takes one expression and an optional clocking event", 3, "20.12"));
}

TEST(ValueChangeArguments, DISABLED_StableWithNoArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $stable());\n"
            "endmodule\n")
          .diags,
      "$stable takes one expression and an optional clocking event", 3,
      "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $stable();\n"
            "endmodule\n")
          .diags,
      "$stable takes one expression and an optional clocking event", 3,
      "20.12"));
}

TEST(ValueChangeArguments,
     DISABLED_StableWithAnEmptyFirstArgumentIsReportedInAnAssertion) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $stable(, @clk));\n"
            "endmodule\n")
          .diags,
      "$stable takes one expression and an optional clocking event", 3,
      "20.12"));
}

TEST(ValueChangeArguments,
     DISABLED_StableWithAnExpressionAsItsSecondArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $stable(a, b));\n"
            "endmodule\n")
          .diags,
      "$stable takes one expression and an optional clocking event", 3,
      "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $stable(a, b);\n"
            "endmodule\n")
          .diags,
      "$stable takes one expression and an optional clocking event", 3,
      "20.12"));
}

TEST(ValueChangeArguments, DISABLED_StableWithAThirdArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $stable(a, @clk, b));\n"
            "endmodule\n")
          .diags,
      "$stable takes one expression and an optional clocking event", 3,
      "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $stable(a,,));\n"
            "endmodule\n")
          .diags,
      "$stable takes one expression and an optional clocking event", 3,
      "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $stable(a, @clk, b);\n"
            "endmodule\n")
          .diags,
      "$stable takes one expression and an optional clocking event", 3,
      "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $stable(a,,);\n"
            "endmodule\n")
          .diags,
      "$stable takes one expression and an optional clocking event", 3,
      "20.12"));
}

TEST(ValueChangeArguments, DISABLED_StableWithADataTypeArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $stable(int));\n"
            "endmodule\n")
          .diags,
      "$stable takes one expression and an optional clocking event", 3,
      "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $stable(int);\n"
            "endmodule\n")
          .diags,
      "$stable takes one expression and an optional clocking event", 3,
      "20.12"));
}

TEST(ValueChangeArguments, DISABLED_ChangedWithNoArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $changed());\n"
            "endmodule\n")
          .diags,
      "$changed takes one expression and an optional clocking event", 3,
      "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $changed();\n"
            "endmodule\n")
          .diags,
      "$changed takes one expression and an optional clocking event", 3,
      "20.12"));
}

TEST(ValueChangeArguments,
     DISABLED_ChangedWithAnEmptyFirstArgumentIsReportedInAnAssertion) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $changed(, @clk));\n"
            "endmodule\n")
          .diags,
      "$changed takes one expression and an optional clocking event", 3,
      "20.12"));
}

TEST(ValueChangeArguments,
     DISABLED_ChangedWithAnExpressionAsItsSecondArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $changed(a, b));\n"
            "endmodule\n")
          .diags,
      "$changed takes one expression and an optional clocking event", 3,
      "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $changed(a, b);\n"
            "endmodule\n")
          .diags,
      "$changed takes one expression and an optional clocking event", 3,
      "20.12"));
}

TEST(ValueChangeArguments, DISABLED_ChangedWithAThirdArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $changed(a, @clk, b));\n"
            "endmodule\n")
          .diags,
      "$changed takes one expression and an optional clocking event", 3,
      "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $changed(a,,));\n"
            "endmodule\n")
          .diags,
      "$changed takes one expression and an optional clocking event", 3,
      "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $changed(a, @clk, b);\n"
            "endmodule\n")
          .diags,
      "$changed takes one expression and an optional clocking event", 3,
      "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $changed(a,,);\n"
            "endmodule\n")
          .diags,
      "$changed takes one expression and an optional clocking event", 3,
      "20.12"));
}

TEST(ValueChangeArguments, DISABLED_ChangedWithADataTypeArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $changed(int));\n"
            "endmodule\n")
          .diags,
      "$changed takes one expression and an optional clocking event", 3,
      "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $changed(int);\n"
            "endmodule\n")
          .diags,
      "$changed takes one expression and an optional clocking event", 3,
      "20.12"));
}

TEST(SampledArguments, OneExpressionIsAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $sampled(a));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  initial x = $sampled(a);\n"
              "endmodule\n"));
}

TEST(SampledArguments, DISABLED_NoArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $sampled());\n"
            "endmodule\n")
          .diags,
      "$sampled takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $sampled();\n"
                                  "endmodule\n")
                                .diags,
                            "$sampled takes exactly one expression argument", 3,
                            "20.12"));
}

TEST(SampledArguments, DISABLED_ASecondExpressionIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $sampled(a, b));\n"
            "endmodule\n")
          .diags,
      "$sampled takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $sampled(a, b);\n"
                                  "endmodule\n")
                                .diags,
                            "$sampled takes exactly one expression argument", 3,
                            "20.12"));
}

TEST(SampledArguments, DISABLED_AnEmptyTrailingArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $sampled(a,));\n"
            "endmodule\n")
          .diags,
      "$sampled takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $sampled(a,);\n"
                                  "endmodule\n")
                                .diags,
                            "$sampled takes exactly one expression argument", 3,
                            "20.12"));
}

TEST(SampledArguments, DISABLED_ADataTypeArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $sampled(int));\n"
            "endmodule\n")
          .diags,
      "$sampled takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $sampled(int);\n"
                                  "endmodule\n")
                                .diags,
                            "$sampled takes exactly one expression argument", 3,
                            "20.12"));
}

TEST(SampledArguments, AClockingEventInAnInitialProcedureIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, clk, x;\n"
            "  initial x = $sampled(a, @(posedge clk));\n"
            "endmodule\n")
          .diags,
      "$sampled does not accept a clocking event argument", 3, "16.9.3"));
}

TEST(SampledArguments, AClockingEventInAModuleFunctionIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, clk;\n"
            "  function logic f();\n"
            "    return $sampled(a, @(posedge clk));\n"
            "  endfunction\n"
            "endmodule\n")
          .diags,
      "$sampled does not accept a clocking event argument", 4, "16.9.3"));
}

TEST(SampledArguments, AClockingEventInAnImmediateAssertionIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, clk;\n"
            "  always @(posedge clk) assert ($sampled(a, @clk));\n"
            "endmodule\n")
          .diags,
      "$sampled does not accept a clocking event argument", 3, "16.9.3"));
}

TEST(SampledArguments, DISABLED_AClockingEventInAConcurrentAssertIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, clk;\n"
            "  assert property (@(posedge clk) $sampled(a, @(posedge clk)));\n"
            "endmodule\n")
          .diags,
      "$sampled does not accept a clocking event argument", 3, "16.9.3"));
}

TEST(SampledArguments, DISABLED_AClockingEventInACoverPropertyIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, clk;\n"
            "  cover property (@(posedge clk) $sampled(a, @clk));\n"
            "endmodule\n")
          .diags,
      "$sampled does not accept a clocking event argument", 3, "16.9.3"));
}

TEST(SampledArguments, AClockingEventInACheckerAlwaysCombIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("checker c(logic a, logic clk);\n"
            "  logic x;\n"
            "  always_comb x = $sampled(a, @(posedge clk));\n"
            "endchecker\n")
          .diags,
      "$sampled does not accept a clocking event argument", 3, "16.9.3"));
}

TEST(SampledArguments, AClockingEventInAPackageFunctionIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("package p;\n"
            "  logic a, clk;\n"
            "  function logic f();\n"
            "    return $sampled(a, @(posedge clk));\n"
            "  endfunction\n"
            "endpackage\n")
          .diags,
      "$sampled does not accept a clocking event argument", 4, "16.9.3"));
}

TEST(PastArguments, AllFourArgumentsAreAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $past(a, 1, g, @clk));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  initial x = $past(a, 1, g, @clk);\n"
              "endmodule\n"));
}

TEST(PastArguments, EmptyTicksAndExpression2BeforeAClockAreAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $past(a, , , @clk));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  initial x = $past(a, , , @clk);\n"
              "endmodule\n"));
}

TEST(PastArguments, EmptyTrailingSlotsAreAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $past(a,));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $past(a,,));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $past(a,,,));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  initial x = $past(a,);\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  initial x = $past(a,,);\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  initial x = $past(a,,,);\n"
              "endmodule\n"));
}

TEST(PastArguments, DISABLED_NoArgumentIsReported) {
  EXPECT_TRUE(
      ReportedError(Parse("module m;\n"
                          "  logic a, b, g, clk, x;\n"
                          "  assert property (@(posedge clk) $past());\n"
                          "endmodule\n")
                        .diags,
                    "$past takes an expression, then optional number_of_ticks, "
                    "expression2 and clocking_event",
                    3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $past();\n"
                                  "endmodule\n")
                                .diags,
                            "$past takes an expression, then optional "
                            "number_of_ticks, expression2 and clocking_event",
                            3, "20.12"));
}

TEST(PastArguments, DISABLED_AClockingEventAsNumberOfTicksIsReported) {
  EXPECT_TRUE(
      ReportedError(Parse("module m;\n"
                          "  logic a, b, g, clk, x;\n"
                          "  assert property (@(posedge clk) $past(a, @clk));\n"
                          "endmodule\n")
                        .diags,
                    "$past takes an expression, then optional number_of_ticks, "
                    "expression2 and clocking_event",
                    3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $past(a, @clk);\n"
                                  "endmodule\n")
                                .diags,
                            "$past takes an expression, then optional "
                            "number_of_ticks, expression2 and clocking_event",
                            3, "20.12"));
}

TEST(PastArguments, DISABLED_AClockingEventAsExpression2IsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $past(a, 1, @clk));\n"
            "endmodule\n")
          .diags,
      "$past takes an expression, then optional number_of_ticks, expression2 "
      "and clocking_event",
      3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $past(a, 1, @clk);\n"
                                  "endmodule\n")
                                .diags,
                            "$past takes an expression, then optional "
                            "number_of_ticks, expression2 and clocking_event",
                            3, "20.12"));
}

TEST(PastArguments, DISABLED_AFifthArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $past(a, 1, g, @clk, b));\n"
            "endmodule\n")
          .diags,
      "$past takes an expression, then optional number_of_ticks, expression2 "
      "and clocking_event",
      3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $past(a, 1, g, @clk, b);\n"
                                  "endmodule\n")
                                .diags,
                            "$past takes an expression, then optional "
                            "number_of_ticks, expression2 and clocking_event",
                            3, "20.12"));
}

TEST(PastArguments, DISABLED_AnEmptyExpression1IsReported) {
  EXPECT_TRUE(
      ReportedError(Parse("module m;\n"
                          "  logic a, b, g, clk, x;\n"
                          "  assert property (@(posedge clk) $past(, 1));\n"
                          "endmodule\n")
                        .diags,
                    "$past takes an expression, then optional number_of_ticks, "
                    "expression2 and clocking_event",
                    3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $past(, 1);\n"
                                  "endmodule\n")
                                .diags,
                            "$past takes an expression, then optional "
                            "number_of_ticks, expression2 and clocking_event",
                            3, "20.12"));
}

TEST(PastArguments, DISABLED_ADataTypeExpression1IsReported) {
  EXPECT_TRUE(
      ReportedError(Parse("module m;\n"
                          "  logic a, b, g, clk, x;\n"
                          "  assert property (@(posedge clk) $past(int));\n"
                          "endmodule\n")
                        .diags,
                    "$past takes an expression, then optional number_of_ticks, "
                    "expression2 and clocking_event",
                    3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $past(int);\n"
                                  "endmodule\n")
                                .diags,
                            "$past takes an expression, then optional "
                            "number_of_ticks, expression2 and clocking_event",
                            3, "20.12"));
}

}  // namespace
