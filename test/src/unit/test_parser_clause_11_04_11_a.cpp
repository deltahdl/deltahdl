#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "simulator/udp_eval.h"

using namespace delta;
namespace {

TEST(ContinuousAssignSyntaxParsing, NetAssignment_TernaryRhs) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, sel, y;\n"
      "  assign y = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_NE(cas[0]->assign_rhs, nullptr);
}
TEST(ProceduralBlockSyntaxParsing, VariableAssignment_TernaryRhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = sel ? a : b; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
}

TEST(OperatorAndExpressionParsing, TernaryInCaseExpr) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (sel ? a : b)\n"
      "      0: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kTernary);
}

TEST(OperatorAndExpressionParsing, TernaryWithSystemCall) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? $random : 0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->true_expr->callee, "$random");
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kIntegerLiteral);
}

TEST(OperatorAndExpressionParsing, TernaryWithUnaryOperands) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? ~a : &b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->true_expr->op, TokenKind::kTilde);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->false_expr->op, TokenKind::kAmp);
}

TEST(OperatorAndExpressionParsing, TernaryAsFunctionArgument) {
  auto r = Parse(
      "module t;\n"
      "  initial x = func(sel ? a : b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
  EXPECT_EQ(rhs->callee, "func");
  ASSERT_EQ(rhs->args.size(), 1u);
  ASSERT_NE(rhs->args[0], nullptr);
  EXPECT_EQ(rhs->args[0]->kind, ExprKind::kTernary);
}

TEST(ExpressionParsing, ConditionalExprSimple) {
  auto r = Parse("module m; initial x = a ? b : c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  ASSERT_NE(rhs->true_expr, nullptr);
  ASSERT_NE(rhs->false_expr, nullptr);
}

TEST(OperatorAndExpressionParsing, TernaryWithCast) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? int'(a) : int'(b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kCast);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kCast);
}

TEST(ProcessParsing, TernaryExpression) {
  auto r = Parse(
      "module m;\n"
      "  logic sel, a, b, y;\n"
      "  always_comb y = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kTernary);
}

TEST(ExpressionParsing, ConditionalExprNested) {
  auto r = Parse("module m; initial x = a ? b ? c : d : e; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kTernary);
}

TEST(ExpressionParsing, ConditionalExprWithBinaryCondition) {
  auto r = Parse("module m; initial x = (a > b) ? a : b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
}

TEST(OperatorAndExpressionParsing, TernaryWithInsideCondition) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if ((a inside {1, 2}) ? x : y) z = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kTernary);
  ASSERT_NE(stmt->condition->condition, nullptr);
  EXPECT_EQ(stmt->condition->condition->kind, ExprKind::kInside);
}

TEST(OperatorAndExpressionParsing, VerifyExprKindTernary) {
  auto r = Parse(
      "module t;\n"
      "  initial x = en ? val_a : val_b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
}

TEST(OperatorAndExpressionParsing, VerifyTernaryFields) {
  auto r = Parse(
      "module t;\n"
      "  initial x = cond_sig ? true_val : false_val;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  VerifyTernaryFieldsAllIdentifier(rhs);
}

TEST(OperatorAndExpressionParsing, TernaryInModulePortConnection) {
  auto r = Parse(
      "module t;\n"
      "  sub u1(.out(sel ? a : b));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FirstModuleInst(r);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->kind, ModuleItemKind::kModuleInst);
  ASSERT_EQ(inst->inst_ports.size(), 1u);
  EXPECT_EQ(inst->inst_ports[0].first, "out");
  ASSERT_NE(inst->inst_ports[0].second, nullptr);
  EXPECT_EQ(inst->inst_ports[0].second->kind, ExprKind::kTernary);
}

TEST(OperatorAndExpressionParsing, TernaryInAlwaysComb) {
  auto r = Parse(
      "module t;\n"
      "  logic sel, a, b, y;\n"
      "  always_comb y = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysCombItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysCombBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kTernary);
}
TEST(OperatorAndExpressionParsing, ConstExprTernaryInLocalparam) {
  auto r = Parse(
      "module t #(parameter A = 1);\n"
      "  localparam B = (A > 0) ? 10 : 20;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(OperatorAndExpressionParsing, TernaryInGenerateIfCondition) {
  auto r = Parse(
      "module t;\n"
      "  parameter A = 1;\n"
      "  parameter B = 0;\n"
      "  if (A ? B : 1) begin\n"
      "    assign x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = FirstGenerateIf(r);
  ASSERT_NE(gen, nullptr);
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_NE(gen->gen_cond, nullptr);
  EXPECT_EQ(gen->gen_cond->kind, ExprKind::kTernary);
}

TEST(OperatorAndExpressionParsing, MultipleTernariesInExpr) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (s1 ? a : b) + (s2 ? c : d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kTernary);
}

TEST(AssignmentParsing, TernaryRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c, sel;\n"
      "  initial begin\n"
      "    a = sel ? b : c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
}

TEST(OperatorAndExpressionParsing, TernaryWithStringLiterals) {
  auto r = Parse(
      "module t;\n"
      "  string s;\n"
      "  initial s = sel ? \"yes\" : \"no\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kStringLiteral);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kStringLiteral);
}

TEST(OperatorAndExpressionParsing, TernaryWithRealLiterals) {
  auto r = Parse(
      "module t;\n"
      "  real r;\n"
      "  initial r = sel ? 3.14 : 2.71;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kRealLiteral);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kRealLiteral);
}

TEST(OperatorAndExpressionParsing, DeeplyNestedTernary) {
  auto r = Parse(
      "module t;\n"
      "  initial x = s1 ? a : s2 ? b : s3 ? c : d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);

  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->false_expr->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->false_expr->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->false_expr->false_expr->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->false_expr->false_expr->kind,
            ExprKind::kIdentifier);
}

TEST(OperatorAndExpressionParsing, TernaryContAssignWithBitSelectLhs) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] out;\n"
      "  wire sel, a, b;\n"
      "  assign out[0] = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kSelect);
  ASSERT_NE(ca->assign_rhs, nullptr);
  EXPECT_EQ(ca->assign_rhs->kind, ExprKind::kTernary);
}
TEST(AggregateTypeParsing, StructTernary) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t x, y, z;\n"
      "  logic sel;\n"
      "  initial z = sel ? x : y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
}

TEST(OperatorAndExpressionParsing, TernaryFieldAccess) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? a : b;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  ASSERT_NE(rhs->true_expr, nullptr);
  ASSERT_NE(rhs->false_expr, nullptr);
}

TEST(OperatorAndExpressionParsing, TernaryTristateDriver) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  wire drive_busa;\n"
              "  wire [15:0] data;\n"
              "  wire [15:0] busa = drive_busa ? data : 16'bz;\n"
              "endmodule\n"));
}

TEST(FormalSyntaxParsing, TernaryExpr) {
  auto r = Parse("module m; initial x = (a > b) ? a : b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
}

TEST(ProcessParsing, TernaryExpressionRHS) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic en, sel;\n"
              "  logic [7:0] q, a, b;\n"
              "  always_latch\n"
              "    if (en) q <= sel ? a : b;\n"
              "endmodule\n"));
}

TEST(ProcessParsing, NestedTernary) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic a, b, c, y;\n"
      "  always_comb y = sel[1] ? (sel[0] ? a : b) : c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kTernary);
}

TEST(OperatorAndExpressionParsing, BitSelectInTernaryCondition) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] flags;\n"
      "  initial x = flags[0] ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  EXPECT_EQ(rhs->condition->kind, ExprKind::kSelect);
  EXPECT_EQ(rhs->condition->index_end, nullptr);
}

TEST(OperatorAndExpressionParsing, SimpleTernary) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  VerifyTernaryFieldsAllIdentifier(rhs);
}

static ModuleItem* FirstContAssign(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) return item;
  }
  return nullptr;
}

TEST(OperatorAndExpressionParsing, TernaryInContAssign) {
  auto r = Parse(
      "module t;\n"
      "  wire sel, a, b, y;\n"
      "  assign y = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_rhs, nullptr);
  EXPECT_EQ(ca->assign_rhs->kind, ExprKind::kTernary);
  ASSERT_NE(ca->assign_rhs->condition, nullptr);
  EXPECT_EQ(ca->assign_rhs->condition->kind, ExprKind::kIdentifier);
  ASSERT_NE(ca->assign_rhs->true_expr, nullptr);
  ASSERT_NE(ca->assign_rhs->false_expr, nullptr);
}

TEST(OperatorAndExpressionParsing, TernaryInBlockingAssign) {
  auto r = Parse(
      "module t;\n"
      "  initial y = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
}

TEST(OperatorAndExpressionParsing, TernaryInNonblockingAssign) {
  auto r = Parse(
      "module t;\n"
      "  reg q;\n"
      "  initial q <= sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
}

TEST(OperatorAndExpressionParsing, NestedTernaryWithParens) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel1 ? (sel2 ? a : b) : c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kIdentifier);
}

TEST(OperatorAndExpressionParsing, TernaryWithComplexCondition) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a > b) ? y : z;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  EXPECT_EQ(rhs->condition->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->condition->op, TokenKind::kGt);
}

TEST(OperatorAndExpressionParsing, TernaryWithBinaryOperands) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? (a + b) : (c - d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->true_expr->op, TokenKind::kPlus);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->false_expr->op, TokenKind::kMinus);
}

TEST(OperatorAndExpressionParsing, TernaryWithFuncCallOperands) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? func(a) : func(b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kCall);
  EXPECT_EQ(rhs->true_expr->callee, "func");
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kCall);
}

TEST(OperatorAndExpressionParsing, TernaryWithConcatenationOperands) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? {a, b} : {c, d};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->true_expr->elements.size(), 2u);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->false_expr->elements.size(), 2u);
}

TEST(OperatorAndExpressionParsing, TernaryWithReplication) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? {4{a}} : {4{b}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kReplicate);
  ASSERT_NE(rhs->true_expr->repeat_count, nullptr);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kReplicate);
}

TEST(OperatorAndExpressionParsing, TernaryWithBitSelectOperands) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial x = sel ? a[3] : b[3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kSelect);
  EXPECT_EQ(rhs->true_expr->index_end, nullptr);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kSelect);
  EXPECT_EQ(rhs->false_expr->index_end, nullptr);
}

TEST(OperatorAndExpressionParsing, TernaryInIfCondition) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (sel ? a : b) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->condition, nullptr);
  EXPECT_EQ(stmt->condition->kind, ExprKind::kTernary);
}

TEST(OperatorAndExpressionParsing, TernaryConditionalFields) {
  auto r = Parse(
      "module t;\n"
      "  initial x = en ? val_a : val_b;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  VerifyTernaryFieldsAllIdentifier(rhs);
}

}  // namespace
