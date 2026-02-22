#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult9h {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult9h Parse(const std::string &src) {
  ParseResult9h result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

// Return the first always-kind module item (any always variant).
static ModuleItem *FirstAlwaysItem(ParseResult9h &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock)
      return item;
  }
  return nullptr;
}

// Return the Nth always-kind module item (0-indexed).
static ModuleItem *NthAlwaysItem(ParseResult9h &r, size_t n) {
  size_t count = 0;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) {
      if (count == n)
        return item;
      ++count;
    }
  }
  return nullptr;
}

// =============================================================================
// LRM section 9.2.2.2 -- always_comb compared with always @*
//
// Both always_comb and always @* describe combinational logic. The parser
// produces AlwaysKind::kAlwaysComb for always_comb and AlwaysKind::kAlways
// for always @*. For always @*, the parser consumes the @* at the
// module-item level (not as a statement-level event control), so both
// forms have the body directly on item->body with empty sensitivity.
// =============================================================================

// ---------------------------------------------------------------------------
// 1. always_comb parses with AlwaysKind::kAlwaysComb.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombAlwaysKind) {
  auto r = Parse("module m;\n"
                 "  always_comb a = b & c;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
}

// ---------------------------------------------------------------------------
// 2. always @* parses with AlwaysKind::kAlways.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarAlwaysKind) {
  auto r = Parse("module m;\n"
                 "  always @* a = b & c;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
}

// ---------------------------------------------------------------------------
// 3. always_comb has empty sensitivity list.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombEmptySensitivity) {
  auto r = Parse("module m;\n"
                 "  always_comb y = a | b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
}

// ---------------------------------------------------------------------------
// 4. always @* also has empty sensitivity (star consumed at module level).
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarEmptySensitivity) {
  auto r = Parse("module m;\n"
                 "  always @* y = a | b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
}

// ---------------------------------------------------------------------------
// 5. always @(*) is equivalent to always @* -- same empty sensitivity.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarParenEquivalent) {
  auto r = Parse("module m;\n"
                 "  always @(*) y = a & b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  EXPECT_TRUE(item->sensitivity.empty());
}

// ---------------------------------------------------------------------------
// 6. always_comb body is directly on item->body (single assignment).
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombBodyDirectAssign) {
  auto r = Parse("module m;\n"
                 "  always_comb x = a ^ b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
}

// ---------------------------------------------------------------------------
// 7. always @* body is directly on item->body (no event control wrapper).
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarBodyDirectAssign) {
  auto r = Parse("module m;\n"
                 "  always @* x = a ^ b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
}

// ---------------------------------------------------------------------------
// 8. always_comb with begin-end block body.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombBeginEndBlock) {
  auto r = Parse("module m;\n"
                 "  always_comb begin\n"
                 "    x = a & b;\n"
                 "    y = a | c;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

// ---------------------------------------------------------------------------
// 9. always @* with begin-end block body.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarBeginEndBlock) {
  auto r = Parse("module m;\n"
                 "  always @* begin\n"
                 "    x = a & b;\n"
                 "    y = a | c;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
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
  auto r = Parse("module m;\n"
                 "  always @(*) begin\n"
                 "    p = q & r;\n"
                 "    s = q | t;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

// ---------------------------------------------------------------------------
// 11. Side-by-side always_comb and always @* in the same module.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_SideBySideBothForms) {
  auto r = Parse("module m;\n"
                 "  always_comb x = a & b;\n"
                 "  always @* y = c | d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *first = NthAlwaysItem(r, 0);
  auto *second = NthAlwaysItem(r, 1);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(first->always_kind, AlwaysKind::kAlwaysComb);
  EXPECT_EQ(second->always_kind, AlwaysKind::kAlways);
}

// ---------------------------------------------------------------------------
// 12. Side-by-side: both have their own body statements.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_SideBySideBodiesExist) {
  auto r = Parse("module m;\n"
                 "  always_comb x = a;\n"
                 "  always @* y = b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *first = NthAlwaysItem(r, 0);
  auto *second = NthAlwaysItem(r, 1);
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
  auto r = Parse("module m;\n"
                 "  always_comb\n"
                 "    if (sel) y = a;\n"
                 "    else y = b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
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
  auto r = Parse("module m;\n"
                 "  always @*\n"
                 "    if (sel) y = a;\n"
                 "    else y = b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
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
  auto r = Parse("module m;\n"
                 "  always_comb\n"
                 "    case (sel)\n"
                 "      2'b00: y = 4'h0;\n"
                 "      2'b01: y = 4'h1;\n"
                 "      default: y = 4'hf;\n"
                 "    endcase\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
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
  auto r = Parse("module m;\n"
                 "  always @*\n"
                 "    case (sel)\n"
                 "      2'b00: y = 4'h0;\n"
                 "      2'b01: y = 4'h1;\n"
                 "      default: y = 4'hf;\n"
                 "    endcase\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
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
  auto r = Parse("module m;\n"
                 "  logic [3:0] a, b, c, y;\n"
                 "  always_comb y = (a > b) ? (a + c) : (b - c);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
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
  auto r = Parse("module m;\n"
                 "  logic [3:0] a, b, c, y;\n"
                 "  always @* y = (a > b) ? (a + c) : (b - c);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kTernary);
}

// ---------------------------------------------------------------------------
// 19. always_comb with variable declarations in begin-end block.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombVarDecls) {
  auto r = Parse("module m;\n"
                 "  always_comb begin\n"
                 "    int temp;\n"
                 "    temp = a + b;\n"
                 "    y = temp;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 3u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->body->stmts[0]->var_name, "temp");
}

// ---------------------------------------------------------------------------
// 20. always @* with variable declarations in begin-end block.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarVarDecls) {
  auto r = Parse("module m;\n"
                 "  always @* begin\n"
                 "    int temp;\n"
                 "    temp = a + b;\n"
                 "    y = temp;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 3u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->body->stmts[0]->var_name, "temp");
}

// ---------------------------------------------------------------------------
// 21. always_comb with function call in body.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombFunctionCall) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  function logic [3:0] mux2(input logic sel,\n"
                      "                            input logic [3:0] a, b);\n"
                      "    return sel ? a : b;\n"
                      "  endfunction\n"
                      "  logic sel;\n"
                      "  logic [3:0] a, b, y;\n"
                      "  always_comb y = mux2(sel, a, b);\n"
                      "endmodule\n"));
}

// ---------------------------------------------------------------------------
// 22. always @* with function call in body.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarFunctionCall) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  function logic [3:0] mux2(input logic sel,\n"
                      "                            input logic [3:0] a, b);\n"
                      "    return sel ? a : b;\n"
                      "  endfunction\n"
                      "  logic sel;\n"
                      "  logic [3:0] a, b, y;\n"
                      "  always @* y = mux2(sel, a, b);\n"
                      "endmodule\n"));
}

// ---------------------------------------------------------------------------
// 23. always_comb with multiple assignment statements.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombMultipleAssigns) {
  auto r = Parse("module m;\n"
                 "  always_comb begin\n"
                 "    x = a & b;\n"
                 "    y = a | c;\n"
                 "    z = a ^ d;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_EQ(item->body->stmts.size(), 3u);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(item->body->stmts[i]->kind, StmtKind::kBlockingAssign);
  }
}

// ---------------------------------------------------------------------------
// 24. always @* with multiple assignment statements.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarMultipleAssigns) {
  auto r = Parse("module m;\n"
                 "  always @* begin\n"
                 "    x = a & b;\n"
                 "    y = a | c;\n"
                 "    z = a ^ d;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_EQ(item->body->stmts.size(), 3u);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(item->body->stmts[i]->kind, StmtKind::kBlockingAssign);
  }
}

// ---------------------------------------------------------------------------
// 25. Stmt-level @* produces kEventControl with is_star_event (not at
//     module level). Contrast with always @* which absorbs @* into the item.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_StmtLevelStarEventIsStarTrue) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @* a = b;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  auto *stmt = body->stmts[0];
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

// ---------------------------------------------------------------------------
// 26. Stmt-level @(*) also sets is_star_event.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_StmtLevelStarParenEventIsStarTrue) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(*) a = b;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  auto *stmt = body->stmts[0];
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

// ---------------------------------------------------------------------------
// 27. always_comb with nested if-else inside begin-end.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombNestedIfElseInBlock) {
  auto r = Parse("module m;\n"
                 "  always_comb begin\n"
                 "    if (a)\n"
                 "      if (b) y = 1;\n"
                 "      else y = 2;\n"
                 "    else\n"
                 "      y = 0;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kIf);
}

// ---------------------------------------------------------------------------
// 28. always @* with nested if-else inside begin-end.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarNestedIfElseInBlock) {
  auto r = Parse("module m;\n"
                 "  always @* begin\n"
                 "    if (a)\n"
                 "      if (b) y = 1;\n"
                 "      else y = 2;\n"
                 "    else\n"
                 "      y = 0;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kIf);
}

// ---------------------------------------------------------------------------
// 29. Both always_comb and always @(*) in the same module with blocks.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_BothFormsWithBlocksInModule) {
  auto r = Parse("module m;\n"
                 "  logic [7:0] a, b, c, x, y;\n"
                 "  always_comb begin\n"
                 "    x = a + b;\n"
                 "  end\n"
                 "  always @(*) begin\n"
                 "    y = b + c;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *comb = NthAlwaysItem(r, 0);
  auto *star = NthAlwaysItem(r, 1);
  ASSERT_NE(comb, nullptr);
  ASSERT_NE(star, nullptr);
  EXPECT_EQ(comb->always_kind, AlwaysKind::kAlwaysComb);
  EXPECT_EQ(star->always_kind, AlwaysKind::kAlways);
  ASSERT_NE(comb->body, nullptr);
  ASSERT_NE(star->body, nullptr);
  EXPECT_EQ(comb->body->kind, StmtKind::kBlock);
  EXPECT_EQ(star->body->kind, StmtKind::kBlock);
}

// ---------------------------------------------------------------------------
// 30. Full combo module: always_comb, always @*, always @(*), with
//     case, if-else, and variable declarations, verifying all parse OK.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_FullComboModuleParseOk) {
  EXPECT_TRUE(ParseOk("module combo_module;\n"
                      "  logic [3:0] sel, a, b, c, d;\n"
                      "  logic [3:0] out1, out2, out3;\n"
                      "  always_comb begin\n"
                      "    int tmp;\n"
                      "    tmp = a + b;\n"
                      "    case (sel)\n"
                      "      4'b0001: out1 = a;\n"
                      "      4'b0010: out1 = b;\n"
                      "      default: out1 = 0;\n"
                      "    endcase\n"
                      "  end\n"
                      "  always @* begin\n"
                      "    int tmp2;\n"
                      "    tmp2 = c - d;\n"
                      "    if (sel[0])\n"
                      "      out2 = c;\n"
                      "    else\n"
                      "      out2 = d;\n"
                      "  end\n"
                      "  always @(*) begin\n"
                      "    out3 = a ^ b ^ c ^ d;\n"
                      "  end\n"
                      "endmodule\n"));
}
