#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// 18.12 / Syntax 18-11: a scope randomize is spelled
//   [ std :: ] randomize ( [ variable_identifier_list ] ) [ with
//   constraint_block ]
// The parser leaves the callee as a plain identifier, so the bare form parses
// as a call whose callee identifier is "randomize" and the std:: form as a call
// whose callee is the "std::randomize" member access. This mirrors the
// IsScopeRandomizeCall recognizer the later stages rely on; here we only assert
// the production yields that shape (the with constraint_block form is exercised
// in §18.12.1's file).
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

// Return the first statement-level call expression in the first initial block.
const Expr* FirstCallInInitial(ParseResult& r) {
  Stmt* body = InitialBody(r);
  if (!body || body->kind != StmtKind::kBlock) return nullptr;
  for (auto* s : body->stmts) {
    if (s && s->expr && s->expr->kind == ExprKind::kCall) return s->expr;
  }
  return nullptr;
}

// 18.12: the variable_identifier_list names the variables to be assigned random
// values. The std:: form with a non-empty list parses to a scope randomize call
// carrying one argument per named variable.
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

// 18.12: the std:: package qualifier is optional, so a bare randomize(...) with
// a variable_identifier_list is the same scope randomize call. The LRM example
// writes the call this way.
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

// 18.12: the variable_identifier_list is optional. A no-argument scope
// randomize parses with an empty argument list — the form the standard
// designates as a constraint checker.
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
