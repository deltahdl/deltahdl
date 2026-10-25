#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kCycleDelayForm =
    "a cycle delay written without parentheses is an integral number or an "
    "identifier; any other expression is parenthesized";

// A.6.11's cycle_delay: `##` and an integral number, `##` and an identifier,
// or `##` and a parenthesized expression, whether it governs a statement
// (A.6.5's procedural_timing_control) or stands in a synchronous drive.
TEST(CycleDelaySyntaxParsing, NumberIdentifierAndParenthesizedFormsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  int n;\n"
      "  initial begin\n"
      "    ##1 n = 1;\n"
      "    ##4'd3 n = 1;\n"
      "    ##n n = 1;\n"
      "    ##\\esc  n = 1;\n"
      "    ##(n + 1) n = 1;\n"
      "    ##(p::N) n = 1;\n"
      "    cb.x <= ##2 1;\n"
      "    cb.x <= ##n 1;\n"
      "    cb.x <= ##(a[0]) 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// Any other primary after a bare `##` is reported where it starts, a name
// under `$root.` or `$unit::` among them, and the statement behind it is still
// read.
TEST(CycleDelaySyntaxParsing, OtherFormsWithoutParenthesesRejected) {
  auto r = Parse(
      "module m;\n"
      "  int n;\n"
      "  initial begin\n"
      "    ##1.5 n = 1;\n"
      "    ##p::N n = 1;\n"
      "    ##f(1) n = 1;\n"
      "    ##'1 n = 1;\n"
      "    ##$ n = 1;\n"
      "    ##null n = 1;\n"
      "    cb.x <= ##a[0] 1;\n"
      "    cb.x <= ##top.n 1;\n"
      "    ##$root.n n = 1;\n"
      "    ##$unit::n n = 1;\n"
      "  end\n"
      "endmodule\n");
  for (uint32_t line = 4; line <= 13; ++line) {
    EXPECT_TRUE(ReportedError(r.diags, kCycleDelayForm, line, "A.6.11"))
        << "line " << line;
  }
}

// A.6.5's clocking_event without parentheses is `@` and a name, plain or
// hierarchical, for a default, a global and a plain clocking declaration alike.
TEST(ClockingDeclarationEventParsing, NamedEventsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  default clocking d @clk; endclocking\n"
      "  global clocking g @top.clk; endclocking\n"
      "  clocking c @\\clk$ ; endclocking\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// An expression written without parentheses leaves what follows its first name
// where the declaration's semicolon belongs, and a name ending in a select is
// no hierarchical identifier (A.9.3).
TEST(ClockingDeclarationEventParsing, ExpressionsWithoutParenthesesRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, en;\n"
      "  logic [1:0] clks;\n"
      "  clocking c1 @clk & en; endclocking\n"
      "  clocking c2 @clks[0]; endclocking\n"
      "  global clocking g @f(clk); endclocking\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got '&'", 4, "14.3"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "an unparenthesized clocking event is '@' and a "
                            "name; an expression is parenthesized",
                            5, "A.6.5"));
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got '('", 6, "14.3"));
}

}  // namespace
