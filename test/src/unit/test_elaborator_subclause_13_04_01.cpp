#include <gtest/gtest.h>

#include <string_view>

#include "elaborator/elaborator.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(FunctionReturnElaboration, FunctionDeclInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  function int add(input int a, input int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FunctionReturnElaboration, VoidFunctionReturnWithValueError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function returns a value", 3, "13.4.1"));
}

TEST(FunctionReturnElaboration,
     ReturnStatementWithAValueInAVoidFunctionNames13_4_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function returns a value", 3, "13.4.1"));
}

TEST(FunctionReturnElaboration, FunctionCallAsExprElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] add_one(input logic [7:0] v);\n"
      "    return v + 8'd1;\n"
      "  endfunction\n"
      "  initial x = add_one(8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionReturnElaboration, NestedCallsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(int n); return n + 1; endfunction\n"
      "  function int g(int n); return n * 2; endfunction\n"
      "  logic [31:0] x;\n"
      "  initial x = f(g(3));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionReturnElaboration, VarSameNameAsFunctionInsideBody) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int foo();\n"
      "    int foo;\n"
      "    foo = 1;\n"
      "    return foo;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of 'foo' conflicts with function name",
                            3, "13.4.1"));
}

TEST(FunctionReturnElaboration, FunctionNameAssignElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int compute(input int a);\n"
      "    compute = a * 2;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionReturnElaboration, VoidFunctionElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function void log(int v);\n"
             "    $display(\"%0d\", v);\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(FunctionReturnElaboration, VoidFunctionBareReturnOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function void f();\n"
             "    $display(\"hello\");\n"
             "    return;\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(FunctionReturnElaboration, NonVoidFunctionBareReturnError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int f();\n"
      "    return;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "return statement in non-void function 'f' gives no value to return", 3,
      "12.8"));
}

TEST(FunctionReturnElaboration, VoidReturnWithValueInNestedBlockError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    if (1) begin\n"
      "      return 42;\n"
      "    end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function returns a value", 4, "13.4.1"));
}

TEST(FunctionReturnElaboration, VoidFunctionAsOperandError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void nop(); endfunction\n"
      "  logic [31:0] x;\n"
      "  initial x = nop();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function 'nop' used as expression operand", 4,
                            "13.4.1"));
}

TEST(FunctionReturnElaboration, VoidFunctionAsStatementOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void nop(); endfunction\n"
      "  initial begin\n"
      "    nop();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionReturnElaboration, VoidFunctionInContAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void nop(); endfunction\n"
      "  wire w;\n"
      "  assign w = nop();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function 'nop' used as expression operand", 4,
                            "13.4.1"));
}

TEST(FunctionReturnElaboration, VoidFunctionAsArgError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void nop(); endfunction\n"
      "  function int f(int x); return x; endfunction\n"
      "  logic [31:0] x;\n"
      "  initial x = f(nop());\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function 'nop' used as expression operand", 5,
                            "13.4.1"));
}

TEST(FunctionReturnElaboration, NonvoidCallAsStatementWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int compute(); return 7; endfunction\n"
      "  initial begin\n"
      "    compute();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(FunctionReturnElaboration, VoidCastSuppressesDiscardWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int compute(); return 7; endfunction\n"
      "  initial begin\n"
      "    void'(compute());\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(FunctionReturnElaboration, VoidCallAsStatementDoesNotWarn) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void nop(); endfunction\n"
      "  initial begin\n"
      "    nop();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(FunctionReturnElaboration, NonvoidCallAsRhsDoesNotWarn) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int compute(); return 7; endfunction\n"
      "  logic [31:0] x;\n"
      "  initial x = compute();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(FunctionReturnElaboration,
     ObjectWithFunctionNameInDeclaringScopeIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int dup(); return 0; endfunction\n"
      "  logic [7:0] dup;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'dup'", 3, "23.9"));
}

TEST(FunctionReturnElaboration, NonvoidCallMissingParensIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int f(); return 1; endfunction\n"
      "  initial begin\n"
      "    f;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot omit parentheses in call to nonvoid "
                            "function 'f'",
                            4, "13.5.5"));
}

TEST(FunctionReturnElaboration, SystemFunctionAllowedAsImplicitVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial x = $random;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionReturnElaboration, VoidFunctionReturnWithValueInsideAForkJoin) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    fork\n"
      "      return 1;\n"
      "    join\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void function returns a value", 4, "13.4.1"));
}

TEST(FunctionReturnElaboration, VarNamedAsFunctionInARandsequenceCodeBlock) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    randsequence(main)\n"
      "      main : { int f; };\n"
      "    endsequence\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of 'f' conflicts with function name",
                            4, "13.4.1"));
}

TEST(FunctionReturnElaboration,
     VarNamedAsFunctionInARandsequenceWeightCodeBlock) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    randsequence(main)\n"
      "      main : alt := 5 { int f; };\n"
      "      alt : { ; };\n"
      "    endsequence\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of 'f' conflicts with function name",
                            4, "13.4.1"));
}

TEST(FunctionReturnElaboration, ValueReturningProductionInAVoidFunctionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    randsequence(main)\n"
      "      void main : a { return; };\n"
      "      int a : { return 7; };\n"
      "    endsequence\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionReturnElaboration, NonvoidFunctionAttachedToASequenceWarns) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  int count;\n"
      "  function int next(int v); return v + 1; endfunction\n"
      "  function void note(int v); endfunction\n"
      "  task tick(int v); endtask\n"
      "  sequence s1; @(posedge clk) (a, next(count)) ##1 b; endsequence\n"
      "  sequence s2; @(posedge clk) (a, note(count)) ##1 b; endsequence\n"
      "  sequence s3; @(posedge clk) (a, tick(count)) ##1 b; endsequence\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(),
      "return value of nonvoid function 'next' is discarded", 7, "13.4.1"));
  EXPECT_EQ(f.diag.WarningCount(), 1u);
}

TEST(FunctionReturnElaboration, SystemFunctionAttachedToASequenceWarns) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  sequence s1; @(posedge clk) (a, $random) ##1 b; endsequence\n"
      "  sequence s2;\n"
      "    @(posedge clk) (a, $urandom_range(3)) ##1 b;\n"
      "  endsequence\n"
      "  sequence s3; @(posedge clk) (a, $display(\"m\")) ##1 b; endsequence\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "nonvoid function '$random' is discarded", 3,
                              "13.4.1"));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "nonvoid function '$urandom_range' is discarded",
                              5, "13.4.1"));
  EXPECT_EQ(f.diag.WarningCount(), 2u);
}

TEST(FunctionReturnElaboration, SystemFunctionCallAsStatementWarns) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int fd;\n"
      "  initial begin\n"
      "    $random;\n"
      "    $fopen(\"f\");\n"
      "    void'($random);\n"
      "    $display(\"x\");\n"
      "    $cast(fd, 3);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "nonvoid function '$random' is discarded", 4,
                              "13.4.1"));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "nonvoid function '$fopen' is discarded", 5,
                              "13.4.1"));
  EXPECT_EQ(f.diag.WarningCount(), 2u);
}

struct MarkedReport {
  const char* src;
  std::string_view marker;
  std::string_view message;
  std::string_view subclause;
};

::testing::AssertionResult ReportedAtMarker(const MarkedReport& r) {
  ElabFixture f;
  ElaborateSrc(r.src, f);
  return ReportedError(f.diag.Diagnostics(), r.message,
                       LineHolding(r.src, r.marker), r.subclause);
}

constexpr std::string_view kVoidOperand = "used as expression operand";
constexpr std::string_view kNameConflict = "conflicts with function name";

TEST(FunctionReturnElaboration,
     AVoidCallAsAnOperandIsReportedInAGenerateBlockSubroutineOrProgram) {
  const MarkedReport kReports[] = {
      {"module t;\n  function void nop();\n  endfunction\n  int x;\n"
       "  if (1) begin : g\n    initial x = nop();\n  end\nendmodule\n",
       "x = nop()", kVoidOperand, "13.4.1"},
      {"module t;\n  function void nop();\n  endfunction\n  int x;\n"
       "  task tk;\n    x = nop();\n  endtask\nendmodule\n",
       "x = nop()", kVoidOperand, "13.4.1"},
      {"module t;\n  function void nop();\n  endfunction\n"
       "  function int g();\n    return nop();\n  endfunction\nendmodule\n",
       "return nop()", kVoidOperand, "13.4.1"},
      {"program p;\n  int x;\n  function void vf();\n  endfunction\n"
       "  initial x = vf();\nendprogram\nmodule t;\n  p u();\nendmodule\n",
       "x = vf()", kVoidOperand, "13.4.1"},
  };
  for (const MarkedReport& r : kReports) {
    SCOPED_TRACE(r.src);
    EXPECT_TRUE(ReportedAtMarker(r));
  }
}

TEST(FunctionReturnElaboration,
     DISABLED_AVoidCallAsAnOperandIsReportedInAnInitializerOrThroughAName) {
  const MarkedReport kReports[] = {
      {"module t;\n  function void nop();\n  endfunction\n"
       "  int v = nop();\nendmodule\n",
       "v = nop()", kVoidOperand, "13.4.1"},
      {"function void uf();\nendfunction\nmodule t;\n  int x;\n"
       "  initial x = uf();\nendmodule\n",
       "x = uf()", kVoidOperand, "13.4.1"},
      {"class C;\n  function void vf();\n  endfunction\nendclass\n"
       "module t;\n  C h = new;\n  int x;\n  initial x = h.vf();\nendmodule\n",
       "x = h.vf()", kVoidOperand, "13.4.1"},
      {"class C;\n  int x;\n  function void vf();\n  endfunction\n"
       "  function void g();\n    x = this.vf();\n  endfunction\nendclass\n"
       "module t;\nendmodule\n",
       "x = this.vf()", kVoidOperand, "13.4.1"},
      {"class B;\n  function void vf();\n  endfunction\nendclass\n"
       "class C extends B;\n  int x;\n  function void g();\n"
       "    x = super.vf();\n  endfunction\nendclass\nmodule t;\nendmodule\n",
       "x = super.vf()", kVoidOperand, "13.4.1"},
      {"module c;\n  function void vf();\n  endfunction\nendmodule\n"
       "module t;\n  c u1();\n  int x;\n  initial x = u1.vf();\nendmodule\n",
       "x = u1.vf()", kVoidOperand, "13.4.1"},
      {"interface i;\n  function void vf();\n  endfunction\nendinterface\n"
       "module c(i b);\n  int x;\n  initial x = b.vf();\nendmodule\n"
       "module t;\n  i u();\n  c v(u);\nendmodule\n",
       "x = b.vf()", kVoidOperand, "13.4.1"},
  };
  for (const MarkedReport& r : kReports) {
    SCOPED_TRACE(r.src);
    EXPECT_TRUE(ReportedAtMarker(r));
  }
}

TEST(FunctionReturnElaboration, AVoidCallAsAStatementIsAcceptedThroughAnyName) {
  EXPECT_TRUE(
      ElabOk("function void uf();\nendfunction\n"
             "class B;\n  function void vf();\n  endfunction\nendclass\n"
             "class C extends B;\n  function void g();\n    vf();\n"
             "    this.vf();\n    super.vf();\n  endfunction\nendclass\n"
             "interface i;\n  function void vf();\n  endfunction\n"
             "endinterface\nmodule c(i b);\n  initial b.vf();\nendmodule\n"
             "module d;\n  function void vf();\n  endfunction\nendmodule\n"
             "module t;\n  C h = new;\n  i u();\n  c v(u);\n  d u1();\n"
             "  initial begin\n    uf();\n    h.vf();\n    h.g();\n"
             "    u1.vf();\n  end\nendmodule\n"));
}

TEST(FunctionReturnElaboration,
     AnObjectNamedLikeAFunctionIsReportedInItsBodyOrDeclaringScope) {
  const MarkedReport kReports[] = {
      {"interface i;\n  function int foo();\n    int foo;\n    return 1;\n"
       "  endfunction\nendinterface\nmodule m;\n  i u();\nendmodule\n",
       "int foo;", kNameConflict, "13.4.1"},
      {"program q;\n  function int foo();\n    int foo;\n    return 1;\n"
       "  endfunction\nendprogram\nmodule m;\n  q u();\nendmodule\n",
       "int foo;", kNameConflict, "13.4.1"},
      {"module m;\n  if (1) begin : g\n    function int foo();\n"
       "      int foo;\n      return 1;\n    endfunction\n  end\nendmodule\n",
       "int foo;", kNameConflict, "13.4.1"},
      {"package p;\n  function int dup(); return 0; endfunction\n"
       "  int dup;\nendpackage\nmodule m;\nendmodule\n",
       "int dup;", "redeclaration of 'dup' in package 'p'", "3.13"},
      {"function int dup(); return 0; endfunction\nint dup;\n"
       "module m;\nendmodule\n",
       "int dup;", "redeclaration of 'dup' in compilation-unit scope", "3.13"},
      {"interface i;\n  function int dup(); return 0; endfunction\n"
       "  int dup;\nendinterface\nmodule m;\n  i u();\nendmodule\n",
       "int dup;", "redeclaration of 'dup'", "23.9"},
      {"program q;\n  function int dup(); return 0; endfunction\n"
       "  int dup;\nendprogram\nmodule m;\n  q u();\nendmodule\n",
       "int dup;", "redeclaration of 'dup'", "23.9"},
      {"module m;\n  if (1) begin : g\n"
       "    function int dup(); return 0; endfunction\n    int dup;\n"
       "  end\nendmodule\n",
       "int dup;", "redeclaration of 'dup'", "23.9"},
      {"module m;\n  logic [7:0] dup;\n"
       "  function int dup(); return 0; endfunction\nendmodule\n",
       "function int dup", "redeclaration of 'dup'", "23.9"},
      {"module m;\n  function int dup(); return 0; endfunction\n"
       "  task dup; endtask\nendmodule\n",
       "task dup", "redeclaration of 'dup'", "23.9"},
  };
  for (const MarkedReport& r : kReports) {
    SCOPED_TRACE(r.src);
    EXPECT_TRUE(ReportedAtMarker(r));
  }
}

TEST(FunctionReturnElaboration,
     DISABLED_AnObjectNamedLikeAFunctionIsReportedAsAFormalOrMember) {
  const MarkedReport kReports[] = {
      {"module m;\n  function int foo(int foo);\n    return 1;\n"
       "  endfunction\nendmodule\n",
       "(int foo)", kNameConflict, "13.4.1"},
      {"package p;\n  function int foo();\n    int foo;\n    return 1;\n"
       "  endfunction\nendpackage\nmodule m;\nendmodule\n",
       "int foo;", kNameConflict, "13.4.1"},
      {"function int foo();\n  int foo;\n  return 1;\nendfunction\n"
       "module m;\nendmodule\n",
       "int foo;", kNameConflict, "13.4.1"},
      {"class C;\n  function int dup(); return 0; endfunction\n"
       "  int dup;\nendclass\nmodule m;\nendmodule\n",
       "int dup;", kNameConflict, "13.4.1"},
  };
  for (const MarkedReport& r : kReports) {
    SCOPED_TRACE(r.src);
    EXPECT_TRUE(ReportedAtMarker(r));
  }
}

TEST(FunctionReturnElaboration, AnObjectNamedOtherThanTheFunctionIsAccepted) {
  EXPECT_TRUE(
      ElabOk("package p;\n  function int foo(int bar);\n    int baz;\n"
             "    return bar;\n  endfunction\n  int dup;\nendpackage\n"
             "function int foo(int bar);\n  int baz;\n  return bar;\n"
             "endfunction\nclass C;\n  function int foo();\n    int baz;\n"
             "    return 0;\n  endfunction\n  int dup;\nendclass\n"
             "module n;\n  int foo;\nendmodule\n"
             "module m;\n  function int foo(int bar);\n    int baz;\n"
             "    return bar;\n  endfunction\n  task tk;\n    int foo;\n"
             "  endtask\n  n u();\nendmodule\n"));
}

TEST(FunctionReturnElaboration,
     DISABLED_ANameAFunctionTakesIsReportedWhenExplicitlyImported) {
  const MarkedReport kReports[] = {
      {"package pk;\n  parameter int F = 100;\nendpackage\nmodule t;\n"
       "  import pk::F;\n  function int F(int x);\n    return x + 1;\n"
       "  endfunction\nendmodule\n",
       "function int F", "collides with existing declaration of 'F'", "26.3"},
      {"package p;\n  function int f(); return 1; endfunction\n"
       "endpackage\nmodule m;\n  import p::f;\n  int f;\nendmodule\n",
       "int f;", "collides with existing declaration of 'f'", "26.3"},
  };
  for (const MarkedReport& r : kReports) {
    SCOPED_TRACE(r.src);
    EXPECT_TRUE(ReportedAtMarker(r));
  }
}

TEST(FunctionReturnElaboration,
     AssigningAnotherParameterInAFunctionIsReportedAsAConstant) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  parameter int G = 7;\n"
      "  function int F(int x);\n"
      "    G = 1;\n"
      "    F = x;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'G'",
                            4, "6.20"));
}

}  // namespace
