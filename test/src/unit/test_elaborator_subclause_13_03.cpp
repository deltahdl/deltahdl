#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(TaskElaboration, TaskDeclInModuleElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task my_task(input int a);\n"
      "    $display(\"a=%0d\", a);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TaskElaboration, TaskWithOutputArgsElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task compute(input int a, output int b);\n"
      "    b = a * 2;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, TaskWithInoutArgElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task inc(inout int v);\n"
      "    v = v + 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, TaskEmptyBodyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task nop;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, TaskEnablesTaskElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task inner;\n"
      "  endtask\n"
      "  task outer;\n"
      "    inner();\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, TaskWithRefArgElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task automatic inc(ref int v);\n"
      "    v = v + 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, RefStaticQualifierStickyInheritedAtElaboration) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task t(ref static int a, b);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->function_decls.size(), 1u);
  auto* tk = mod->function_decls[0];
  ASSERT_EQ(tk->func_args.size(), 2u);
  EXPECT_EQ(tk->func_args[0].direction, Direction::kRef);
  EXPECT_TRUE(tk->func_args[0].is_ref_static);
  EXPECT_EQ(tk->func_args[1].direction, Direction::kRef);
  EXPECT_TRUE(tk->func_args[1].is_ref_static);
}

TEST(TaskElaboration, ReturnValueDeclaredNames13_3) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    return 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "task returns a value", 3, "13.3"));
}

TEST(TaskElaboration, ReturnValueInAnAssertionPassStmtIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    assert (1) return 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "task returns a value", 3, "13.3"));
}

TEST(TaskElaboration, ReturnValueInAnAssertionFailStmtIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    assert (1) else return 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "task returns a value", 3, "13.3"));
}

TEST(TaskElaboration, ReturnValueInARandcaseItemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    randcase 1 : return 1; endcase\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "task returns a value", 3, "13.3"));
}

TEST(TaskElaboration, ValueReturningProductionInATaskOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    randsequence(main)\n"
      "      void main : a { return; };\n"
      "      int a : { return 7; };\n"
      "    endsequence\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, ImportedTaskAsAnExpressionOperandIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  import \"DPI-C\" task t(input int a);\n"
      "  int x;\n"
      "  initial x = t(1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 't' is enabled from a statement and cannot "
                            "be an operand of an expression",
                            4, "13.3"));
}

TEST(TaskElaboration, NativeTaskAsAnExpressionOperandIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t(input int a);\n"
      "  endtask\n"
      "  int x;\n"
      "  initial x = t(1) + 2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 't' is enabled from a statement and cannot "
                            "be an operand of an expression",
                            5, "13.3"));
}

TEST(TaskElaboration, TaskEnabledAsAStatementBesideAFunctionOperandOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t(input int a);\n"
      "  endtask\n"
      "  function int g(input int a);\n"
      "    return a;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial begin\n"
      "    t(1);\n"
      "    x = g(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, TaskOperandInContinuousAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  task t; endtask\n"
      "  assign y = t();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 't' is enabled from a statement and "
                            "cannot be an operand of an expression",
                            4, "13.3"));
}

TEST(TaskElaboration, TaskOperandInDeclarationInitializerError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t; endtask\n"
      "  int v = t();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 't' is enabled from a statement and "
                            "cannot be an operand of an expression",
                            3, "13.3"));
}

TEST(TaskElaboration, TaskOperandInGenerateBlockError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  task t; endtask\n"
      "  if (1) begin : g\n"
      "    initial x = t();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 't' is enabled from a statement and "
                            "cannot be an operand of an expression",
                            5, "13.3"));
}

TEST(TaskElaboration, PackageAndUnitTaskOperandsError) {
  ElabFixture f;
  ElaborateSrc(
      "package pk; task t; endtask endpackage\n"
      "task u; endtask\n"
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = pk::t();\n"
      "    x = u();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 'pk::t' is enabled from a statement and "
                            "cannot be an operand of an expression",
                            6, "13.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 'u' is enabled from a statement and cannot "
                            "be an operand of an expression",
                            7, "13.3"));
}

TEST(TaskElaboration, ModuleFunctionHidesUnitTask) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "task u; endtask\n"
      "module m;\n"
      "  int x;\n"
      "  function int u(); return 1; endfunction\n"
      "  initial x = u();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, TaskOperandInGenerateElseAndCaseArmsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  task t; endtask\n"
      "  if (0) begin : a\n"
      "  end else begin : b\n"
      "    initial x = t();\n"
      "  end\n"
      "  case (1)\n"
      "    1: begin : c\n"
      "      initial x = t();\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 't' is enabled from a statement and "
                            "cannot be an operand of an expression",
                            6, "13.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 't' is enabled from a statement and "
                            "cannot be an operand of an expression",
                            10, "13.3"));
}

TEST(TaskElaboration, BodyDeclarationTypingADirectionOnlyFormalElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task mytask2;\n"
      "    output x;\n"
      "    input y;\n"
      "    int x;\n"
      "    logic y;\n"
      "    x = y;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, BodyDeclarationThatTypesNoFormalIsARedeclaration) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task t;\n"
      "    input int a;\n"
      "    input b;\n"
      "    input c;\n"
      "    int a;\n"
      "    int b = 1;\n"
      "    localparam int c = 2;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'a'", 6, "23.9"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'b'", 7, "23.9"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'c'", 8, "23.9"));
}

}  // namespace
