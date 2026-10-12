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

// §13.4 rule (b): a function cannot enable a task, and A.8.2's optional
// argument list makes `t;` an enable of t (#6424).
TEST(FunctionElaboration, FunctionEnablingATaskByItsBareNameError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t; endtask\n"
      "  function void f();\n"
      "    t;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function cannot enable a task", 4, "13.4"));
}

// The same for a task declared in a package or at compilation-unit scope
// (#6425).
TEST(FunctionElaboration, FunctionEnablingAPackageOrUnitTaskError) {
  ElabFixture f;
  ElaborateSrc(
      "package pk; task t; endtask endpackage\n"
      "task u; endtask\n"
      "module m;\n"
      "  function void f();\n"
      "    pk::t();\n"
      "    u();\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function cannot enable a task", 5, "13.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function cannot enable a task", 6, "13.4"));
}

// §13.4: a function with an output, inout or ref argument is called neither in
// an event expression, which an assignment's intra-assignment event control
// holds (#6429), nor in an expression outside every procedural statement,
// which a module variable's initializer is (#6430).
TEST(FunctionElaboration, OutputArgumentCallInIntraAssignmentEventError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  logic y;\n"
      "  function logic f(output logic o); o = 1; return 1; endfunction\n"
      "  initial a = @(f(y)) b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'f' has output argument; cannot be "
                            "called in an event expression",
                            5, "13.4"));
}

TEST(FunctionElaboration, OutputArgumentCallInModuleInitializerError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  function int f(output logic o); o = 1; return 1; endfunction\n"
      "  int v = f(y);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'f' has output argument; cannot be "
                            "called in a declaration's initializer",
                            4, "13.4"));
}

}  // namespace
