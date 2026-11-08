#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;
namespace {

bool IsBareScopeRandomize(const Expr* e) {
  return e && e->kind == ExprKind::kCall && e->lhs &&
         e->lhs->kind == ExprKind::kIdentifier && e->lhs->text == "randomize";
}

bool IsStdScopeRandomize(const Expr* e) {
  return e && e->kind == ExprKind::kCall && e->lhs &&
         e->lhs->kind == ExprKind::kMemberAccess && e->lhs->rhs &&
         e->lhs->rhs->kind == ExprKind::kIdentifier &&
         e->lhs->rhs->text == "randomize" && e->lhs->lhs &&
         e->lhs->lhs->kind == ExprKind::kIdentifier &&
         e->lhs->lhs->text == "std";
}

const Expr* FirstCallInInitial(ParseResult& r) {
  Stmt* body = InitialBody(r);
  if (!body || body->kind != StmtKind::kBlock) return nullptr;
  for (auto* s : body->stmts) {
    if (s && s->expr && s->expr->kind == ExprKind::kCall) return s->expr;
  }
  return nullptr;
}

TEST(ScopeRandomizeParsing, StdFormWithVariableList) {
  auto r = Parse(
      "module stim;\n"
      "  initial begin\n"
      "    bit [15:0] addr;\n"
      "    bit [31:0] data;\n"
      "    bit rd_wr;\n"
      "    std::randomize(addr, data, rd_wr);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  const Expr* call = FirstCallInInitial(r);
  ASSERT_NE(call, nullptr);
  EXPECT_TRUE(IsStdScopeRandomize(call));
  EXPECT_EQ(call->args.size(), 3u);
}

TEST(ScopeRandomizeParsing, BareFormWithVariableList) {
  auto r = Parse(
      "module stim;\n"
      "  initial begin\n"
      "    bit [15:0] addr;\n"
      "    bit [31:0] data;\n"
      "    bit rd_wr;\n"
      "    randomize(addr, data, rd_wr);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  const Expr* call = FirstCallInInitial(r);
  ASSERT_NE(call, nullptr);
  EXPECT_TRUE(IsBareScopeRandomize(call));
  EXPECT_EQ(call->args.size(), 3u);
}

TEST(ScopeRandomizeParsing, NoArgumentForm) {
  auto r = Parse(
      "module stim;\n"
      "  initial begin\n"
      "    std::randomize();\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  const Expr* call = FirstCallInInitial(r);
  ASSERT_NE(call, nullptr);
  EXPECT_TRUE(IsStdScopeRandomize(call));
  EXPECT_TRUE(call->args.empty());
}

}  // namespace
