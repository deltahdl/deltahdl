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

}  // namespace
