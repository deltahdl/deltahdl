// §11.2.1: Constant expressions

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.8.3 Expressions — constant_expression
// =============================================================================
// § constant_expression ::= constant_primary
TEST(ParserA83, ConstantExprPrimary) {
  auto r = Parse(
      "module m #(parameter int P = 42);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& params = r.cu->modules[0]->params;
  ASSERT_GE(params.size(), 1u);
  EXPECT_EQ(params[0].second->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(params[0].second->int_val, 42u);
}

struct ParseResult11e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11e Parse(const std::string& src) {
  ParseResult11e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =========================================================================
// Section 11.2.1 -- Constant expressions (operands)
// =========================================================================
TEST(ParserSection11, ConstExprInParamDecl) {
  auto r = Parse(
      "module t;\n"
      "  parameter WIDTH = 8;\n"
      "  parameter DEPTH = 2 ** WIDTH;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
