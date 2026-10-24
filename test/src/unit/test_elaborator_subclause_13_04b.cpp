#include <gtest/gtest.h>

#include <cstdint>

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

// Footnote 25 of Syntax 13-1 and 13-2 bars the specifiers from every task and
// function that is no method declared in a class, a package's and the
// compilation unit's among them. These were reported in a module alone.
TEST(FunctionElaboration, DynamicOverrideOnPackageAndUnitSubroutinesError) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  function :initial void f(); endfunction\n"
      "  task :final t(); endtask\n"
      "endpackage\n"
      "function :extends void g(); endfunction\n"
      "module m; endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const char* const kFunction =
      "a function's dynamic_override_specifiers belong on a class method "
      "declaration, and an interface class takes none";
  EXPECT_TRUE(ReportedError(diags, kFunction, 2, "13.4"));
  EXPECT_TRUE(ReportedError(diags,
                            "a task's dynamic_override_specifiers belong on a "
                            "class method declaration, and an interface class "
                            "takes none",
                            3, "13.3"));
  EXPECT_TRUE(ReportedError(diags, kFunction, 5, "13.4"));
}

// The same footnote reaches a definition written outside its class (§8.24) or
// through an interface prefix (§25.7): the class's own prototype carries the
// specifiers, and §8.20's Example 3 has the external definition declare none.
// So `C::f5` and `b.put` are reported, while C's prototypes and `C::f6`, which
// writes none, are not. Each definition's prefix exempted it.
TEST(FunctionElaboration, DynamicOverrideOnOutOfBlockDefinitionError) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  extern function :initial void f5();\n"
      "  extern function :final void f6();\n"
      "endclass\n"
      "function :initial void C::f5(); endfunction\n"
      "function void C::f6(); endfunction\n"
      "interface bus;\n"
      "  extern function void put(int d);\n"
      "endinterface\n"
      "module m (bus b);\n"
      "  function :final void b.put(int d); endfunction\n"
      "endmodule\n"
      "module top;\n"
      "  bus i ();\n"
      "  m u (i);\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const char* const kFunction =
      "a function's dynamic_override_specifiers belong on a class method "
      "declaration, and an interface class takes none";
  for (uint32_t line : {5u, 11u}) {
    EXPECT_TRUE(ReportedError(diags, kFunction, line, "13.4")) << line;
  }
  for (uint32_t line : {2u, 3u, 6u}) {
    EXPECT_FALSE(ReportedError(diags, kFunction, line, "13.4")) << line;
  }
}

}  // namespace
