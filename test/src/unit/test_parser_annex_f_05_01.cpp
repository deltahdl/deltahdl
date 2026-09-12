#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

// Annex F.5.1: rewrite rules for clocks.
//
// F.5.1 defines a clocked sequence's or property's semantics through the
// unclocked one its rewrite rules produce, and makes that rewrite depend on a
// condition: no event control's condition may depend on a local variable,
// since the rules push each clock's condition down onto the Booleans it
// clocks, where a local variable of the sequence or property has a value the
// clock cannot read. §16.10 states the same as a rule of the language, that a
// local variable is not to be used in a clocking event expression, and the
// parser reports it there. The cases below hold the report to every local a
// sequence or property has: one declared in the body and one that is a local
// variable formal argument, in a property as in a sequence, where only a
// sequence's body local was reported.

using namespace delta;

namespace {

std::string InClockingEvent(const std::string& name) {
  return "local variable \"" + name +
         "\" may not be used in a clocking event expression";
}

// A property body local named in the property's clocking event.
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

// The clock stands inside the property rather than leading it, and the local
// is read through an iff guard rather than as the edge's signal.
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

// The local stands inside a parenthesized condition of the guard, which the
// reader of the event group has to enter rather than take as the group's end.
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

// An event group the source never closes ends at the end of the file, and the
// local read before that end is still reported.
TEST(ClockRewritePrecondition, AnUnclosedEventGroupIsReadToTheEndOfTheFile) {
  auto r = Parse(
      "module m;\n"
      "  property p;\n"
      "    int v;\n"
      "    @(posedge v");
  EXPECT_TRUE(ReportedError(r.diags, InClockingEvent("v"), 4, "16.10"));
}

// A local variable formal argument is a local variable of the property
// (§16.8.2), so a clock on it is under the same condition.
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

// And a sequence's local variable formal argument, which the sequence's body
// scan held to its body locals alone.
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

// The controls: a formal that is not local may clock the property, and a
// property whose clock reads an ordinary signal keeps its locals for the
// Booleans, where F.5.1's rewrite has no condition on them.
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

}  // namespace
