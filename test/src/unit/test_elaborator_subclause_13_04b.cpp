#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §13.4 rule (a) bars a function from any statement containing `#` or `@`,
// and a blocking assignment's intra-assignment delay or event control is one
// the assignment contains: it suspends the calling process (#5919).
TEST(FunctionElaboration, IntraAssignmentDelayInFunctionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  function void f();\n"
      "    a = #1 b;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 4,
      "13.4"));
}

TEST(FunctionElaboration, IntraAssignmentEventControlInFunctionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  event e;\n"
      "  function void f();\n"
      "    a = @(e) b;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 5,
      "13.4"));
}

// A nonblocking assignment's intra-assignment delay is a `#` the statement
// contains as well.
TEST(FunctionElaboration, NonblockingIntraAssignmentDelayInFunctionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  function void f();\n"
      "    a <= #1 b;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "time-controlling statement is not allowed inside a function", 4,
      "13.4"));
}

// §13.4.4 lets a fork-join_none in a function hold what a task may, an
// intra-assignment delay among it.
TEST(FunctionElaboration, IntraAssignmentDelayUnderJoinNoneAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  function void f();\n"
      "    fork\n"
      "      a = #1 b;\n"
      "    join_none\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
