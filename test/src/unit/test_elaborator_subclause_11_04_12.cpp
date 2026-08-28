#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "helpers_eval_op.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ConcatenationSim, ConcatWithVariables) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 4'hC;\n"
      "    b = 4'h3;\n"
      "    result = {a, b};\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xC3u);
}

TEST(ConcatenationSim, ConcatDoesNotInterfere) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = {4'h1, 4'h2};\n"
      "  initial b = 8'd99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0x12u);
  EXPECT_EQ(vb->value.ToUint64(), 99u);
}

TEST(ConcatenationElaboration, ConcatenationInContAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] x, y;\n"
      "  assign a = {x, y};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConcatenationElaboration, ConstantConcatenationInParam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter [15:0] P = {8'hAB, 8'hCD};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConcatenationSim, ConcatInAlwaysComb) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] hi, lo;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    hi = 4'hA;\n"
      "    lo = 4'hB;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = {hi, lo};\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(ConcatenationSim, LhsConcatUnpacking) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  initial {a, b} = 8'hC3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0xCu);
  EXPECT_EQ(vb->value.ToUint64(), 0x3u);
}

TEST(ConcatenationSim, ConcatThreeVariables) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b, c;\n"
      "  logic [11:0] result;\n"
      "  initial begin\n"
      "    a = 4'hA;\n"
      "    b = 4'hB;\n"
      "    c = 4'hC;\n"
      "    result = {a, b, c};\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCu);
}

TEST(ConcatenationSim, NestedConcatSim) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b, c;\n"
      "  logic [11:0] result;\n"
      "  initial begin\n"
      "    a = 4'h1;\n"
      "    b = 4'h2;\n"
      "    c = 4'h3;\n"
      "    result = {a, {b, c}};\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x123u);
}

TEST(ConcatenationElaboration, UnsizedConstantInConcatRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] x;\n"
      "  initial a = {x, 1};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unsized constant is not allowed in a concatenation", 4, "11.4.12"));
}

TEST(ConcatenationElaboration, SelectOnConcatLvalueRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  initial {a, b}[2] = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "select of a concatenation shall not be used as an lvalue",
                    3, "11.4.12"));
}

TEST(ConcatenationElaboration, UnsizedConstantInNestedConcatRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [11:0] a;\n"
      "  logic [3:0] x;\n"
      "  initial a = {x, {x, 7}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unsized constant is not allowed in a concatenation", 4, "11.4.12"));
}

TEST(ConcatenationElaboration, PartSelectOnConcatLvalueRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  initial {a, b}[3:0] = 4'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "select of a concatenation shall not be used as an lvalue",
                    3, "11.4.12"));
}

TEST(ConcatenationElaboration, SelectOnConcatNetLvalueRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [3:0] a, b;\n"
      "  assign {a, b}[2] = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "select of a concatenation shall not be used as an lvalue",
                    3, "11.4.12"));
}

TEST(ConcatenationSim, ConcatMixedWidths) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] b;\n"
      "  logic [11:0] result;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "    b = 4'hC;\n"
      "    result = {a, b};\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCu);
}

// §11.4.12 says "Unsized constant numbers shall not be allowed in
// concatenations", a property of the concatenation and not of the statement
// holding it.
//
// ElaboratorOperationRules::WalkStmtsForUnsizedInConcat in
// src/elaborator/elaborator_validate_operations_arrays.cpp reached six of the
// thirteen statement links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h states. The seven cases here
// each put `a = {x, 1}` in one of the seven positions it did not read, every
// one of which elaborated clean beforehand.
//
// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword [ :
// block_identifier ]`, so a fork arm is a statement position like any other.
TEST(ConcatenationElaboration, UnsizedConstantInConcatInAForkArmNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = {x, 1};\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unsized constant is not allowed in a concatenation", 6, "11.4.12"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case covers
// the pass arm and the one below it the fail arm.
TEST(ConcatenationElaboration,
     UnsizedConstantInConcatInAnAssertionPassStatementNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] x;\n"
      "  logic ok;\n"
      "  initial assert (ok) a = {x, 1};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unsized constant is not allowed in a concatenation", 5, "11.4.12"));
}

TEST(ConcatenationElaboration,
     UnsizedConstantInConcatInAnAssertionFailStatementNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] x;\n"
      "  logic ok;\n"
      "  initial assert (ok) else a = {x, 1};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unsized constant is not allowed in a concatenation", 5, "11.4.12"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. The rule
// is a static one, so it holds whether the weighted draw would select the item
// or not.
TEST(ConcatenationElaboration,
     UnsizedConstantInConcatInARandcaseItemNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] x;\n"
      "  initial randcase 1: a = {x, 1}; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unsized constant is not allowed in a concatenation", 4, "11.4.12"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions.
TEST(ConcatenationElaboration,
     UnsizedConstantInConcatInARandsequenceCodeBlockNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { a = {x, 1}; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unsized constant is not allowed in a concatenation", 6, "11.4.12"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments |
// for_variable_declaration { , for_variable_declaration }` and
// `for_step_assignment ::= operator_assignment | inc_or_dec_expression |
// function_subroutine_call`. A.6.2 gives `variable_assignment ::=
// variable_lvalue = expression` and `operator_assignment ::= variable_lvalue
// assignment_operator expression`, whose assignment_operator includes `=`, so
// an assignment stands at each of the two positions: this case writes one at
// the initialization and the case below it writes one at the step.
TEST(ConcatenationElaboration,
     UnsizedConstantInConcatInAForLoopInitializationNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] x;\n"
      "  int i;\n"
      "  initial for (a = {x, 1}; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unsized constant is not allowed in a concatenation", 5, "11.4.12"));
}

TEST(ConcatenationElaboration,
     UnsizedConstantInConcatInAForLoopStepNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] x;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; a = {x, 1}) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unsized constant is not allowed in a concatenation", 5, "11.4.12"));
}

}  // namespace
