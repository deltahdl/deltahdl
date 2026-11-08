#include <gtest/gtest.h>

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

}  // namespace
