// §20.8.1: Integer math functions

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserCh50603, SystemFunction_InExpression) {
  // A system function like $clog2 used inside an expression.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter W = $clog2(256);\n"
              "endmodule"));
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

TEST(ParserSection11, ConstExprSystemFuncInParam) {
  auto r = Parse(
      "module t;\n"
      "  parameter N = 16;\n"
      "  parameter BITS = $clog2(N);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8.2 Subroutine calls — system_tf_call
// =============================================================================
// § system_tf_call ::= system_tf_identifier [ ( list_of_arguments ) ]
//   | system_tf_identifier ( data_type [ , expression ] )
//   | system_tf_identifier ( expression { , [ expression ] } ... )
// system_tf_call as expression ($clog2 returns a value)
TEST(ParserA82, SystemTfCallAsExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial x = $clog2(256);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->rhs->callee, "$clog2");
  EXPECT_EQ(stmt->rhs->args.size(), 1u);
}

// =============================================================================
// A.8.4 Primaries — system calls as primary
// =============================================================================
// § primary — system function call
TEST(ParserA84, PrimarySystemCall) {
  auto r = Parse("module m; initial x = $clog2(16); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
}

}  // namespace
