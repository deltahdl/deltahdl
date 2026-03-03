// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

struct ParseResult9h {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9h Parse(const std::string& src) {
  ParseResult9h result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// Return the first always-kind module item (any always variant).
static ModuleItem* FirstAlwaysItem(ParseResult9h& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) return item;
  }
  return nullptr;
}

namespace {

// ---------------------------------------------------------------------------
// 17. always_comb with complex combinational logic (nested ternary).
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombComplexLogic) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] a, b, c, y;\n"
      "  always_comb y = (a > b) ? (a + c) : (b - c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kTernary);
}

// ---------------------------------------------------------------------------
// 18. always @* with complex combinational logic (nested ternary).
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarComplexLogic) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] a, b, c, y;\n"
      "  always @* y = (a > b) ? (a + c) : (b - c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kTernary);
}

}  // namespace
