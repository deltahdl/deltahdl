// §6.24.1: Cast operator

#include "elaborator/type_eval.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// LRM section 6.20 -- Type operator
// =============================================================================
TEST(ParserSection6, TypeExprInCast) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = int'(3.14);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

static Stmt* FirstInitialStmt(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

// =========================================================================
// §6.24: Casting — general
// =========================================================================
TEST(ParserSection6, CastUnsigned) {
  // §6.24: unsigned'(expr) changes signedness.
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  initial x = unsigned'(y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCast);
  EXPECT_EQ(rhs->text, "unsigned");
}

}  // namespace
