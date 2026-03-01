// Annex A.6.4: Statements

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §13: function_statement_or_null — null statement in function body
TEST(ParserA604, FunctionStatementOrNullWithNull) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    ;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  EXPECT_EQ(func->func_body_stmts[0]->kind, StmtKind::kNull);
}

// §13: function_statement with label
TEST(ParserA604, FunctionStatementWithLabel) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    step1: a = 1;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  EXPECT_EQ(func->func_body_stmts[0]->label, "step1");
}

// §13: function_statement with attribute
TEST(ParserA604, FunctionStatementWithAttribute) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    (* inline *) a = 1;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  EXPECT_FALSE(func->func_body_stmts[0]->attrs.empty());
  EXPECT_EQ(func->func_body_stmts[0]->attrs[0].name, "inline");
}

}  // namespace
