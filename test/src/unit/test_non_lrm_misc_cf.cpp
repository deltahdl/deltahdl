// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

struct ParseResult11d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11d Parse(const std::string& src) {
  ParseResult11d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult11d& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static Expr* FirstAssignRhs(ParseResult11d& r) {
  auto* stmt = FirstInitialStmt(r);
  if (!stmt) return nullptr;
  return stmt->rhs;
}

namespace {

TEST(ParserSection11, OperatorPrecedenceMixedArithRhs) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a + b * c;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kStar);
}

TEST(ParserSection11, OperatorPrecedenceCompareAndLogical) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a > 0) && (b < 10);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kAmpAmp);
}

// =========================================================================
// Section 11.5.1 -- Bit-select and part-select
// =========================================================================
TEST(ParserSection11, BitSelect) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a[3];\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
}

TEST(ParserSection11, PartSelectConstant) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a[7:0];\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
}

// =========================================================================
// Section 11.3.5 -- Short-circuit evaluation
// =========================================================================
TEST(ParserSection11, ShortCircuitAnd) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a != 0) && (b / a > 1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =========================================================================
// Section 11.7 -- Signed expressions ($signed, $unsigned)
// =========================================================================
TEST(ParserSection11, SignedSystemCall) {
  auto r = Parse(
      "module t;\n"
      "  initial x = $signed(a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$signed");
}

TEST(ParserSection11, UnsignedSystemCall) {
  auto r = Parse(
      "module t;\n"
      "  initial x = $unsigned(a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$unsigned");
}

// --- Streaming operator with type-sized slice (§11.4.14) ---
TEST(ParserSection11, StreamingWithTypedSlice) {
  auto r = Parse(
      "module t;\n"
      "  byte a;\n"
      "  int b;\n"
      "  initial b = {<< byte {a}};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- Tagged union expressions (§11.9) ---
TEST(ParserSection11, TaggedUnionExpr) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    int a;\n"
      "    a = tagged Invalid;\n"
      "    a = tagged Valid (42);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
