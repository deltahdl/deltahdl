#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult11g {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11g Parse(const std::string& src) {
  ParseResult11g result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static Stmt* FirstInitialStmt(ParseResult11g& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static Expr* FirstAssignRhs(ParseResult11g& r) {
  auto* stmt = FirstInitialStmt(r);
  if (!stmt) return nullptr;
  return stmt->rhs;
}

static ModuleItem* FirstContAssign(ParseResult11g& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) return item;
  }
  return nullptr;
}

static ModuleItem* FirstAlwaysCombItem(ParseResult11g& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysCombBlock) return item;
  }
  return nullptr;
}

static ModuleItem* FirstModuleInst(ParseResult11g& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kModuleInst) return item;
  }
  return nullptr;
}

static ModuleItem* FirstGenerateIf(ParseResult11g& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) return item;
  }
  return nullptr;
}

// =========================================================================
// LRM section 11.4.6 -- Conditional operator (ternary ? :)
// =========================================================================

// --- Simple ternary: sel ? a : b ---

TEST(ParserSection11, Sec11_4_6_SimpleTernary) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  EXPECT_EQ(rhs->condition->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kIdentifier);
}

// --- Ternary in continuous assignment ---

TEST(ParserSection11, Sec11_4_6_TernaryInContAssign) {
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

// --- Ternary in blocking assignment ---

TEST(ParserSection11, Sec11_4_6_TernaryInBlockingAssign) {
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

// --- Ternary in nonblocking assignment ---

TEST(ParserSection11, Sec11_4_6_TernaryInNonblockingAssign) {
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

// --- Nested ternary with parentheses ---

TEST(ParserSection11, Sec11_4_6_NestedTernaryWithParens) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel1 ? (sel2 ? a : b) : c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kIdentifier);
}

// --- Chained ternary without parens (right-associative) ---

TEST(ParserSection11, Sec11_4_6_ChainedTernaryRightAssoc) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel1 ? a : sel2 ? b : c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kIdentifier);
  // Right-associative: false_expr is itself a ternary.
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->false_expr->true_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->true_expr->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->false_expr->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->false_expr->kind, ExprKind::kIdentifier);
}

// --- Ternary with complex condition ---

TEST(ParserSection11, Sec11_4_6_TernaryWithComplexCondition) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a > b) ? y : z;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  EXPECT_EQ(rhs->condition->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->condition->op, TokenKind::kGt);
}

// --- Ternary with binary expression operands ---

TEST(ParserSection11, Sec11_4_6_TernaryWithBinaryOperands) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? (a + b) : (c - d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->true_expr->op, TokenKind::kPlus);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->false_expr->op, TokenKind::kMinus);
}

// --- Ternary with function call operands ---

TEST(ParserSection11, Sec11_4_6_TernaryWithFuncCallOperands) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? func(a) : func(b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kCall);
  EXPECT_EQ(rhs->true_expr->callee, "func");
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kCall);
}

// --- Ternary with concatenation operands ---

TEST(ParserSection11, Sec11_4_6_TernaryWithConcatenationOperands) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? {a, b} : {c, d};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->true_expr->elements.size(), 2u);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->false_expr->elements.size(), 2u);
}

// --- Ternary with replication operands ---

TEST(ParserSection11, Sec11_4_6_TernaryWithReplication) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? {4{a}} : {4{b}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kReplicate);
  ASSERT_NE(rhs->true_expr->repeat_count, nullptr);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kReplicate);
}

// --- Ternary with bit-select operands ---

TEST(ParserSection11, Sec11_4_6_TernaryWithBitSelectOperands) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial x = sel ? a[3] : b[3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kSelect);
  EXPECT_EQ(rhs->true_expr->index_end, nullptr);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kSelect);
  EXPECT_EQ(rhs->false_expr->index_end, nullptr);
}

// --- Ternary with part-select operands ---

TEST(ParserSection11, Sec11_4_6_TernaryWithPartSelectOperands) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial x = sel ? a[7:4] : b[7:4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->true_expr->index, nullptr);
  ASSERT_NE(rhs->true_expr->index_end, nullptr);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->false_expr->index_end, nullptr);
}

// --- Ternary in if condition ---

TEST(ParserSection11, Sec11_4_6_TernaryInIfCondition) {
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

// --- Ternary in case expression ---

TEST(ParserSection11, Sec11_4_6_TernaryInCaseExpr) {
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

// --- Ternary with system call operand ---

TEST(ParserSection11, Sec11_4_6_TernaryWithSystemCall) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? $random : 0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->true_expr->callee, "$random");
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kIntegerLiteral);
}

// --- Ternary with unary operands ---

TEST(ParserSection11, Sec11_4_6_TernaryWithUnaryOperands) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? ~a : &b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->true_expr->op, TokenKind::kTilde);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->false_expr->op, TokenKind::kAmp);
}

// --- Ternary as function argument ---

TEST(ParserSection11, Sec11_4_6_TernaryAsFunctionArgument) {
  auto r = Parse(
      "module t;\n"
      "  initial x = func(sel ? a : b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
  EXPECT_EQ(rhs->callee, "func");
  ASSERT_EQ(rhs->args.size(), 1u);
  ASSERT_NE(rhs->args[0], nullptr);
  EXPECT_EQ(rhs->args[0]->kind, ExprKind::kTernary);
}

// --- Ternary with cast operands ---

TEST(ParserSection11, Sec11_4_6_TernaryWithCast) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel ? int'(a) : int'(b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kCast);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kCast);
}

// --- Ternary with inside condition ---

TEST(ParserSection11, Sec11_4_6_TernaryWithInsideCondition) {
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

// --- Verify ExprKind::kTernary kind ---

TEST(ParserSection11, Sec11_4_6_VerifyExprKindTernary) {
  auto r = Parse(
      "module t;\n"
      "  initial x = en ? val_a : val_b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
}

// --- Verify condition, true_expr, false_expr fields ---

TEST(ParserSection11, Sec11_4_6_VerifyTernaryFields) {
  auto r = Parse(
      "module t;\n"
      "  initial x = cond_sig ? true_val : false_val;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  EXPECT_EQ(rhs->condition->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kIdentifier);
}

// --- Ternary in module port connection ---

TEST(ParserSection11, Sec11_4_6_TernaryInModulePortConnection) {
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

// --- Ternary in always_comb ---

TEST(ParserSection11, Sec11_4_6_TernaryInAlwaysComb) {
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

// --- Ternary in generate if condition ---

TEST(ParserSection11, Sec11_4_6_TernaryInGenerateIfCondition) {
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

// --- Multiple ternaries in same expression ---

TEST(ParserSection11, Sec11_4_6_MultipleTernariesInExpr) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (s1 ? a : b) + (s2 ? c : d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kTernary);
}

// --- Ternary with string literal operands ---

TEST(ParserSection11, Sec11_4_6_TernaryWithStringLiterals) {
  auto r = Parse(
      "module t;\n"
      "  string s;\n"
      "  initial s = sel ? \"yes\" : \"no\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kStringLiteral);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kStringLiteral);
}

// --- Ternary with real literal operands ---

TEST(ParserSection11, Sec11_4_6_TernaryWithRealLiterals) {
  auto r = Parse(
      "module t;\n"
      "  real r;\n"
      "  initial r = sel ? 3.14 : 2.71;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kRealLiteral);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kRealLiteral);
}

// --- Deeply nested ternary (three levels) ---

TEST(ParserSection11, Sec11_4_6_DeeplyNestedTernary) {
  auto r = Parse(
      "module t;\n"
      "  initial x = s1 ? a : s2 ? b : s3 ? c : d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  // s1 ? a : (s2 ? b : (s3 ? c : d))
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->false_expr->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->false_expr->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->false_expr->false_expr->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->false_expr->false_expr->kind,
            ExprKind::kIdentifier);
}

// --- Ternary in continuous assignment with complex LHS ---

TEST(ParserSection11, Sec11_4_6_TernaryContAssignWithBitSelectLhs) {
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
