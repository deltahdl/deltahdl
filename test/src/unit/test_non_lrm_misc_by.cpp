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

// Return the Nth always-kind module item (0-indexed).
static ModuleItem* NthAlwaysItem(ParseResult9h& r, size_t n) {
  size_t count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) {
      if (count == n) return item;
      ++count;
    }
  }
  return nullptr;
}

namespace {

// ---------------------------------------------------------------------------
// 23. always_comb with complex combinational logic (priority encoder)
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_PriorityEncoderPattern) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] req;\n"
      "  logic [1:0] enc;\n"
      "  logic valid;\n"
      "  always_comb begin\n"
      "    enc = 2'b00;\n"
      "    valid = 1'b0;\n"
      "    if (req[3]) begin\n"
      "      enc = 2'b11;\n"
      "      valid = 1'b1;\n"
      "    end else if (req[2]) begin\n"
      "      enc = 2'b10;\n"
      "      valid = 1'b1;\n"
      "    end else if (req[1]) begin\n"
      "      enc = 2'b01;\n"
      "      valid = 1'b1;\n"
      "    end else if (req[0]) begin\n"
      "      enc = 2'b00;\n"
      "      valid = 1'b1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  // Two default assignments plus an if-else-if chain
  ASSERT_GE(item->body->stmts.size(), 3u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(item->body->stmts[1]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(item->body->stmts[2]->kind, StmtKind::kIf);
}

// ---------------------------------------------------------------------------
// 9. always @* with begin-end block body.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  always @* begin\n"
      "    x = a & b;\n"
      "    y = a | c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

// ---------------------------------------------------------------------------
// 10. always @(*) with begin-end block body.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarParenBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  always @(*) begin\n"
      "    p = q & r;\n"
      "    s = q | t;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

// ---------------------------------------------------------------------------
// 11. Side-by-side always_comb and always @* in the same module.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_SideBySideBothForms) {
  auto r = Parse(
      "module m;\n"
      "  always_comb x = a & b;\n"
      "  always @* y = c | d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* first = NthAlwaysItem(r, 0);
  auto* second = NthAlwaysItem(r, 1);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(first->always_kind, AlwaysKind::kAlwaysComb);
  EXPECT_EQ(second->always_kind, AlwaysKind::kAlways);
}

// ---------------------------------------------------------------------------
// 12. Side-by-side: both have their own body statements.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_SideBySideBodiesExist) {
  auto r = Parse(
      "module m;\n"
      "  always_comb x = a;\n"
      "  always @* y = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* first = NthAlwaysItem(r, 0);
  auto* second = NthAlwaysItem(r, 1);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  ASSERT_NE(first->body, nullptr);
  ASSERT_NE(second->body, nullptr);
  EXPECT_EQ(first->body->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(second->body->kind, StmtKind::kBlockingAssign);
}

// ---------------------------------------------------------------------------
// 13. always_comb with if-else body.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombIfElse) {
  auto r = Parse(
      "module m;\n"
      "  always_comb\n"
      "    if (sel) y = a;\n"
      "    else y = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kIf);
  EXPECT_NE(item->body->then_branch, nullptr);
  EXPECT_NE(item->body->else_branch, nullptr);
}

// ---------------------------------------------------------------------------
// 14. always @* with if-else body.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarIfElse) {
  auto r = Parse(
      "module m;\n"
      "  always @*\n"
      "    if (sel) y = a;\n"
      "    else y = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kIf);
  EXPECT_NE(item->body->then_branch, nullptr);
  EXPECT_NE(item->body->else_branch, nullptr);
}

// ---------------------------------------------------------------------------
// 15. always_comb with case statement.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombCaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  always_comb\n"
      "    case (sel)\n"
      "      2'b00: y = 4'h0;\n"
      "      2'b01: y = 4'h1;\n"
      "      default: y = 4'hf;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_GE(item->body->case_items.size(), 3u);
}

// ---------------------------------------------------------------------------
// 16. always @* with case statement.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarCaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  always @*\n"
      "    case (sel)\n"
      "      2'b00: y = 4'h0;\n"
      "      2'b01: y = 4'h1;\n"
      "      default: y = 4'hf;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_GE(item->body->case_items.size(), 3u);
}

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
