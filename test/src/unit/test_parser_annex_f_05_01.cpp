#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string InClockingEvent(const std::string& name) {
  return "local variable \"" + name +
         "\" may not be used in a clocking event expression";
}

TEST(ClockRewritePrecondition, APropertyBodyLocalInItsClockIsReported) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    logic v;\n"
      "    @(posedge v) (a, v = b) |-> c;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, InClockingEvent("v"), 4, "16.10"));
}

TEST(ClockRewritePrecondition, APropertyLocalInANestedClockGuardIsReported) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    int v;\n"
      "    @(posedge clk) (a, v = b) |-> @(posedge clk iff v) c;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, InClockingEvent("v"), 4, "16.10"));
}

TEST(ClockRewritePrecondition, APropertyLocalInAParenthesizedGuardIsReported) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    int v;\n"
      "    @(posedge clk iff (v == 1)) (a, v = b) |-> c;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, InClockingEvent("v"), 4, "16.10"));
}

TEST(ClockRewritePrecondition, AnUnclosedEventGroupIsReadToTheEndOfTheFile) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    int v;\n"
      "    @(posedge v");
  EXPECT_TRUE(ReportedError(r.diags, InClockingEvent("v"), 4, "16.10"));
}

TEST(ClockRewritePrecondition, APropertyLocalFormalInItsClockIsReported) {
  auto r = Parse(
      "module m;\n"
      "  property p(local input logic v);\n"
      "    @(posedge v) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, InClockingEvent("v"), 3, "16.10"));
}

TEST(ClockRewritePrecondition, ASequenceLocalFormalInItsClockIsReported) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local input logic v);\n"
      "    @(posedge v) a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, InClockingEvent("v"), 3, "16.10"));
}

TEST(ClockRewritePrecondition, AFormalThatIsNotLocalMayClockTheProperty) {
  auto r = Parse(
      "module m;\n"
      "  property p(logic v);\n"
      "    @(posedge v) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClockRewritePrecondition, APropertyLocalOutsideTheClockIsNotReported) {
  auto r = Parse(
      "module m;\n"
      "  property p(local input int w);\n"
      "    int v;\n"
      "    @(posedge clk) (a, v = w) |-> ##1 (b == v);\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

std::string Replaced(std::string text, const std::string& from,
                     const std::string& to) {
  for (std::size_t at = text.find(from); at != std::string::npos;
       at = text.find(from, at + to.size())) {
    text.replace(at, from.size(), to);
  }
  return text;
}

std::string InModule(const std::string& decl) {
  return "module m;\n  logic clk, a, b;\n" + decl + "endmodule\n";
}

void ExpectReportedClock(const std::string& src) {
  auto bad = Parse(Replaced(src, "CLK", "v"));
  EXPECT_TRUE(ReportedError(bad.diags, InClockingEvent("v"), 5, "16.10"))
      << src;
  auto good = Parse(Replaced(src, "CLK", "clk"));
  EXPECT_FALSE(good.has_errors) << src;
}

std::string SequenceWith(const std::string& body) {
  return "  sequence s;\n    logic v;\n    " + body + ";\n  endsequence\n";
}

std::string PropertyWith(const std::string& body) {
  return "  property p;\n    logic v;\n    " + body + ";\n  endproperty\n";
}

TEST(ClockRewritePrecondition, ASequenceLocalInALaterClockIsReported) {
  ExpectReportedClock(
      InModule(SequenceWith("@(posedge clk) (a, v = b) ##1 @(posedge CLK) b")));
}

TEST(ClockRewritePrecondition, APropertyLocalAsALaterClocksEdgeIsReported) {
  ExpectReportedClock(
      InModule(PropertyWith("@(posedge clk) (a, v = b) |-> @(posedge CLK) b")));
}

TEST(ClockRewritePrecondition, ASequenceLocalInItsLeadingGuardIsReported) {
  ExpectReportedClock(
      InModule(SequenceWith("@(posedge clk iff CLK) (a, v = b) ##1 (v == b)")));
}

TEST(ClockRewritePrecondition, ALocalAsAWholeClockIsReported) {
  ExpectReportedClock(InModule(SequenceWith("@(CLK) (a, v = b) ##1 b")));
  ExpectReportedClock(InModule(PropertyWith("@(CLK) (a, v = b) |-> b")));
}

TEST(ClockRewritePrecondition, DISABLED_ALocalAsABareNamedClockIsReported) {
  ExpectReportedClock(InModule(SequenceWith("@CLK (a, v = b) ##1 b")));
  ExpectReportedClock(InModule(PropertyWith("@CLK (a, v = b) |-> b")));
}

TEST(ClockRewritePrecondition, ALocalUnderEachEdgeIsReported) {
  for (const char* edge : {"posedge", "negedge", "edge"}) {
    ExpectReportedClock(InModule(
        SequenceWith("@(" + std::string(edge) + " CLK) (a, v = b) ##1 b")));
  }
}

TEST(ClockRewritePrecondition, ALocalInAnEventListIsReported) {
  ExpectReportedClock(
      InModule(SequenceWith("@(posedge clk or negedge CLK) (a, v = b) ##1 b")));
  ExpectReportedClock(
      InModule(PropertyWith("@(posedge CLK, negedge a) (a, v = b) |-> b")));
}

TEST(ClockRewritePrecondition, ALocalInsideACompoundClockIsReported) {
  ExpectReportedClock(
      InModule(SequenceWith("@(posedge (clk & !CLK)) (a, v = b) ##1 b")));
}

TEST(ClockRewritePrecondition, ALocalPassedToAnInstanceUsedAsAClockIsReported) {
  ExpectReportedClock(InModule(SequenceWith("@(t(CLK)) (a, v = b) ##1 b")));
  ExpectReportedClock(InModule(PropertyWith("@(t(CLK)) (a, v = b) |-> b")));
}

TEST(ClockRewritePrecondition, ALocalInASampledValueFunctionsClockIsReported) {
  for (const char* call :
       {"$rose(a, @(posedge CLK))", "$fell(a, @(posedge CLK))",
        "$stable(a, @(posedge CLK))", "$changed(a, @(posedge CLK))",
        "$past(a, 1, 1, @(posedge CLK))"}) {
    const std::string kCall = call;
    ExpectReportedClock(
        InModule(SequenceWith("@(posedge clk) (a, v = b) ##1 " + kCall)));
    ExpectReportedClock(
        InModule(PropertyWith("@(posedge clk) (a, v = b) |-> " + kCall)));
  }
}

TEST(ClockRewritePrecondition, ALocalHidingAClockSignalIsReported) {
  auto r =
      Parse(InModule("  sequence s;\n"
                     "    logic clk;\n"
                     "    @(posedge clk) (a, clk = b) ##1 b;\n"
                     "  endsequence\n"));
  EXPECT_TRUE(ReportedError(r.diags, InClockingEvent("clk"), 5, "16.10"));
}

TEST(ClockRewritePrecondition, AnotherDeclarationsLocalMayNameAClockSignal) {
  auto r =
      Parse(InModule("  sequence s;\n"
                     "    logic a;\n"
                     "    @(posedge clk) (b, a = b) ##1 a;\n"
                     "  endsequence\n"
                     "  property p;\n"
                     "    @(posedge a) b;\n"
                     "  endproperty\n"));
  EXPECT_FALSE(r.has_errors);
}

std::string AnyClock(const std::string& decl) {
  std::string text =
      Replaced(decl, "S_HEAD", "sequence s;\n    logic v;\n    ");
  text = Replaced(text, "P_HEAD", "property p;\n    logic v;\n    ");
  text = Replaced(text, "S_TAIL", "endsequence\n");
  return Replaced(text, "P_TAIL", "endproperty\n");
}

TEST(ClockRewritePrecondition, ADirectFormIsReportedInEveryScope) {
  const std::string kScopes[][2] = {
      {"interface i;\n  logic clk, a, b;\n", "endinterface\n"},
      {"program g;\n  logic clk, a, b;\n", "endprogram\n"},
      {"checker c;\n  logic clk, a, b;\n", "endchecker\n"},
      {"package k;\n  logic clk, a, b;\n", "endpackage\n"},
      {"logic clk;\nlogic a, b;\n", ""},
      {"module m; logic clk, a, b;\n  if (1) begin : g\n", "end endmodule\n"}};
  const std::string kDecls[] = {
      "S_HEAD@(posedge CLK) (a, v = b) ##1 b; S_TAIL",
      "S_HEAD@(posedge clk) (a, v = b) ##1 @(posedge CLK) b; S_TAIL",
      "S_HEAD@(posedge clk iff CLK) (a, v = b) ##1 b; S_TAIL",
      "S_HEAD@(CLK) (a, v = b) ##1 b; S_TAIL",
      "S_HEAD@(t(CLK)) (a, v = b) ##1 b; S_TAIL",
      "S_HEAD@(posedge clk) (a, v = b) ##1 $rose(a, @(posedge CLK)); S_TAIL",
      "P_HEAD@(posedge CLK) (a, v = b) |-> b; P_TAIL",
      "P_HEAD@(posedge clk) (a, v = b) |-> @(posedge CLK) b; P_TAIL",
      "P_HEAD@(posedge clk iff CLK) (a, v = b) |-> b; P_TAIL",
      "P_HEAD@(CLK) (a, v = b) |-> b; P_TAIL",
      "P_HEAD@(posedge clk) (a, v = b) |-> $fell(a, @(posedge CLK)); P_TAIL"};
  for (const auto& scope : kScopes) {
    for (const auto& decl : kDecls) {
      ExpectReportedClock(scope[0] + AnyClock("  " + decl) + scope[1]);
    }
  }
}

}  // namespace
