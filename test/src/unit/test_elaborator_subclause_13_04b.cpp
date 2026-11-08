#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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
