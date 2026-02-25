// Non-LRM tests

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {


// ---------------------------------------------------------------------------
// 19. always_comb with variable declarations in begin-end block.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombVarDecls) {
  auto r = Parse(
      "module m;\n"
      "  always_comb begin\n"
      "    int temp;\n"
      "    temp = a + b;\n"
      "    y = temp;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
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
  auto r = Parse(
      "module m;\n"
      "  always @* begin\n"
      "    int temp;\n"
      "    temp = a + b;\n"
      "    y = temp;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
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
  EXPECT_TRUE(
      ParseOk("module m;\n"
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
  EXPECT_TRUE(
      ParseOk("module m;\n"
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
  auto r = Parse(
      "module m;\n"
      "  always_comb begin\n"
      "    x = a & b;\n"
      "    y = a | c;\n"
      "    z = a ^ d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
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
  auto r = Parse(
      "module m;\n"
      "  always @* begin\n"
      "    x = a & b;\n"
      "    y = a | c;\n"
      "    z = a ^ d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
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
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @* a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  auto* stmt = body->stmts[0];
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

// ---------------------------------------------------------------------------
// 26. Stmt-level @(*) also sets is_star_event.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_StmtLevelStarParenEventIsStarTrue) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(*) a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  auto* stmt = body->stmts[0];
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

// ---------------------------------------------------------------------------
// 27. always_comb with nested if-else inside begin-end.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysCombNestedIfElseInBlock) {
  auto r = Parse(
      "module m;\n"
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
  auto* item = FirstAlwaysItem(r);
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
  auto r = Parse(
      "module m;\n"
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
  auto* item = FirstAlwaysItem(r);
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
  auto r = Parse(
      "module m;\n"
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
  auto* comb = NthAlwaysItem(r, 0);
  auto* star = NthAlwaysItem(r, 1);
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
  EXPECT_TRUE(
      ParseOk("module combo_module;\n"
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

struct ParseResult9i {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9i Parse(const std::string& src) {
  ParseResult9i result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstAlwaysLatchItem(ParseResult9i& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysLatchBlock) return item;
  }
  return nullptr;
}

static ModuleItem* NthAlwaysLatchItem(ParseResult9i& r, size_t n) {
  size_t count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      if (count == n) return item;
      ++count;
    }
  }
  return nullptr;
}

// =============================================================================
// LRM section 9.2.3 -- Always_latch procedure
//
// The always_latch procedure models latched logic.  It has an implicit
// sensitivity list (no @(...) clause) and is expected to infer latches.
// =============================================================================
// ---------------------------------------------------------------------------
// 1. Simple if-else latch pattern -- the canonical always_latch usage.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_SimpleIfElseLatch) {
  auto r = Parse(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch\n"
      "    if (en) q <= d;\n"
      "    else q <= q;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysLatchBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kIf);
  EXPECT_NE(item->body->then_branch, nullptr);
  EXPECT_NE(item->body->else_branch, nullptr);
}

// ---------------------------------------------------------------------------
// 2. always_latch with begin-end block wrapping the body.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_BeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch begin\n"
      "    if (en) q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysLatchBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kIf);
}

// ---------------------------------------------------------------------------
// 3. if without else -- transparent latch (no else retains state).
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_IfWithoutElse) {
  auto r = Parse(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch\n"
      "    if (en) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kIf);
  EXPECT_NE(item->body->condition, nullptr);
  EXPECT_NE(item->body->then_branch, nullptr);
  EXPECT_EQ(item->body->else_branch, nullptr);
}

// ---------------------------------------------------------------------------
// 4. always_latch with case statement body.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_CaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] q, a, b;\n"
      "  always_latch\n"
      "    case (sel)\n"
      "      2'b00: q <= a;\n"
      "      2'b01: q <= b;\n"
      "      default: q <= q;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_EQ(item->body->case_kind, TokenKind::kKwCase);
  EXPECT_GE(item->body->case_items.size(), 3u);
}

// ---------------------------------------------------------------------------
// 5. Nested if-else chain.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_NestedIfElse) {
  auto r = Parse(
      "module m;\n"
      "  logic en1, en2, d1, d2, q;\n"
      "  always_latch\n"
      "    if (en1)\n"
      "      q <= d1;\n"
      "    else if (en2)\n"
      "      q <= d2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kIf);
  // The else branch is itself an if statement.
  ASSERT_NE(item->body->else_branch, nullptr);
  EXPECT_EQ(item->body->else_branch->kind, StmtKind::kIf);
}

// ---------------------------------------------------------------------------
// 6. Multiple assignments inside a begin-end block.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_MultipleAssignments) {
  auto r = Parse(
      "module m;\n"
      "  logic en, d1, d2, q1, q2;\n"
      "  always_latch begin\n"
      "    if (en) begin\n"
      "      q1 <= d1;\n"
      "      q2 <= d2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  auto* if_stmt = item->body->stmts[0];
  EXPECT_EQ(if_stmt->kind, StmtKind::kIf);
  ASSERT_NE(if_stmt->then_branch, nullptr);
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kBlock);
  EXPECT_EQ(if_stmt->then_branch->stmts.size(), 2u);
}

// ---------------------------------------------------------------------------
// 7. Complex conditions (logical operators in if expression).
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_ComplexConditions) {
  auto r = Parse(
      "module m;\n"
      "  logic en, valid, d, q;\n"
      "  always_latch\n"
      "    if (en && valid) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kIf);
  ASSERT_NE(item->body->condition, nullptr);
  EXPECT_EQ(item->body->condition->kind, ExprKind::kBinary);
}

// ---------------------------------------------------------------------------
// 8. Bit select on LHS of assignment.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_BitSelect) {
  auto r = Parse(
      "module m;\n"
      "  logic en;\n"
      "  logic [7:0] q, d;\n"
      "  always_latch\n"
      "    if (en) q[3] <= d[3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  auto* if_stmt = item->body;
  EXPECT_EQ(if_stmt->kind, StmtKind::kIf);
  ASSERT_NE(if_stmt->then_branch, nullptr);
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(if_stmt->then_branch->lhs, nullptr);
  EXPECT_EQ(if_stmt->then_branch->lhs->kind, ExprKind::kSelect);
}

// ---------------------------------------------------------------------------
// 9. Part select on LHS of assignment.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_PartSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic en;\n"
              "  logic [7:0] q, d;\n"
              "  always_latch\n"
              "    if (en) q[3:0] <= d[3:0];\n"
              "endmodule\n"));
}

// ---------------------------------------------------------------------------
// 10. Struct member access in assignment.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_StructMemberAccess) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct packed {\n"
              "    logic [7:0] data;\n"
              "    logic valid;\n"
              "  } packet_t;\n"
              "  packet_t pkt;\n"
              "  logic en;\n"
              "  logic [7:0] d;\n"
              "  always_latch\n"
              "    if (en) pkt.data <= d;\n"
              "endmodule\n"));
}

// ---------------------------------------------------------------------------
// 11. Function call in RHS expression.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_FunctionCallRHS) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function logic [7:0] compute(input logic [7:0] x);\n"
              "    return x + 1;\n"
              "  endfunction\n"
              "  logic en;\n"
              "  logic [7:0] q, d;\n"
              "  always_latch\n"
              "    if (en) q <= compute(d);\n"
              "endmodule\n"));
}

// ---------------------------------------------------------------------------
// 12. Ternary expression in RHS.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_TernaryExpressionRHS) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic en, sel;\n"
              "  logic [7:0] q, a, b;\n"
              "  always_latch\n"
              "    if (en) q <= sel ? a : b;\n"
              "endmodule\n"));
}

// ---------------------------------------------------------------------------
// 13. Variable declaration inside always_latch begin-end block.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_VarDeclInBlock) {
  auto r = Parse(
      "module m;\n"
      "  logic en;\n"
      "  logic [7:0] q, d;\n"
      "  always_latch begin\n"
      "    logic [7:0] tmp;\n"
      "    tmp = d + 1;\n"
      "    if (en) q <= tmp;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 3u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kVarDecl);
}

// ---------------------------------------------------------------------------
// 14. unique case statement inside always_latch.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_UniqueCaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] q, a, b, c;\n"
      "  always_latch\n"
      "    unique case (sel)\n"
      "      2'b00: q <= a;\n"
      "      2'b01: q <= b;\n"
      "      2'b10: q <= c;\n"
      "      default: q <= q;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_EQ(item->body->qualifier, CaseQualifier::kUnique);
}

// ---------------------------------------------------------------------------
// 15. priority case statement inside always_latch.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_PriorityCaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] q, a, b;\n"
      "  always_latch\n"
      "    priority case (sel)\n"
      "      2'b00: q <= a;\n"
      "      2'b01: q <= b;\n"
      "      default: q <= q;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_EQ(item->body->qualifier, CaseQualifier::kPriority);
}

// ---------------------------------------------------------------------------
// 16. for loop inside always_latch.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_ForLoop) {
  auto r = Parse(
      "module m;\n"
      "  logic en;\n"
      "  logic [7:0] q [0:3];\n"
      "  logic [7:0] d [0:3];\n"
      "  always_latch begin\n"
      "    for (int i = 0; i < 4; i++)\n"
      "      if (en) q[i] <= d[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kFor);
  EXPECT_NE(item->body->stmts[0]->for_cond, nullptr);
  EXPECT_NE(item->body->stmts[0]->for_body, nullptr);
}

// ---------------------------------------------------------------------------
// 17. Verify ModuleItemKind is kAlwaysLatchBlock.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_ModuleItemKindIsAlwaysLatchBlock) {
  auto r = Parse(
      "module m;\n"
      "  always_latch\n"
      "    if (en) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      found = true;
      EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
    }
  }
  EXPECT_TRUE(found);
}

// ---------------------------------------------------------------------------
// 18. always_latch has no sensitivity list (implicit).
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_NoSensitivityList) {
  auto r = Parse(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch\n"
      "    if (en) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
}

// ---------------------------------------------------------------------------
// 19. Multiple always_latch blocks in the same module.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_MultipleAlwaysLatchBlocks) {
  auto r = Parse(
      "module m;\n"
      "  logic en1, en2, d1, d2, q1, q2;\n"
      "  always_latch\n"
      "    if (en1) q1 <= d1;\n"
      "  always_latch\n"
      "    if (en2) q2 <= d2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* first = NthAlwaysLatchItem(r, 0);
  auto* second = NthAlwaysLatchItem(r, 1);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(first->kind, ModuleItemKind::kAlwaysLatchBlock);
  EXPECT_EQ(second->kind, ModuleItemKind::kAlwaysLatchBlock);
}

// ---------------------------------------------------------------------------
// 20. casex inside always_latch.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_CasexStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] sel, q, a, b;\n"
      "  always_latch\n"
      "    casex (sel)\n"
      "      4'b1xxx: q <= a;\n"
      "      4'b01xx: q <= b;\n"
      "      default: q <= q;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_EQ(item->body->case_kind, TokenKind::kKwCasex);
}

// ---------------------------------------------------------------------------
// 21. casez inside always_latch.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_CasezStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] sel, q, a, b;\n"
      "  always_latch\n"
      "    casez (sel)\n"
      "      4'b1???: q <= a;\n"
      "      4'b01??: q <= b;\n"
      "      default: q <= q;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_EQ(item->body->case_kind, TokenKind::kKwCasez);
}

// ---------------------------------------------------------------------------
// 22. Body verification: if-statement has correct condition and then branch.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_BodyVerificationIfCondition) {
  auto r = Parse(
      "module m;\n"
      "  logic gate, d, q;\n"
      "  always_latch\n"
      "    if (gate) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  auto* body = item->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kIf);
  ASSERT_NE(body->condition, nullptr);
  ASSERT_NE(body->then_branch, nullptr);
  EXPECT_EQ(body->then_branch->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(body->then_branch->lhs, nullptr);
  EXPECT_NE(body->then_branch->rhs, nullptr);
}

// ---------------------------------------------------------------------------
// 23. always_latch with blocking assignments (combinational style).
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_BlockingAssignment) {
  auto r = Parse(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch\n"
      "    if (en) q = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  auto* if_stmt = item->body;
  EXPECT_EQ(if_stmt->kind, StmtKind::kIf);
  ASSERT_NE(if_stmt->then_branch, nullptr);
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kBlockingAssign);
}

// ---------------------------------------------------------------------------
// 24. always_latch with ternary in condition.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_TernaryInCondition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic sel, en_a, en_b, d, q;\n"
              "  always_latch\n"
              "    if (sel ? en_a : en_b) q <= d;\n"
              "endmodule\n"));
}

// ---------------------------------------------------------------------------
// 25. always_latch with concatenation on LHS.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_ConcatenationLHS) {
  auto r = Parse(
      "module m;\n"
      "  logic en;\n"
      "  logic [3:0] a, b, d;\n"
      "  always_latch\n"
      "    if (en) {a, b} <= {d, d};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  auto* if_stmt = item->body;
  ASSERT_NE(if_stmt, nullptr);
  ASSERT_NE(if_stmt->then_branch, nullptr);
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(if_stmt->then_branch->lhs, nullptr);
  EXPECT_EQ(if_stmt->then_branch->lhs->kind, ExprKind::kConcatenation);
}

// ---------------------------------------------------------------------------
// 26. unique0 case inside always_latch.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_Unique0CaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] q, a, b;\n"
      "  always_latch\n"
      "    unique0 case (sel)\n"
      "      2'b00: q <= a;\n"
      "      2'b01: q <= b;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_EQ(item->body->qualifier, CaseQualifier::kUnique0);
}

// ---------------------------------------------------------------------------
// 27. always_latch with deeply nested if-else-if chain.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_DeepIfElseIfChain) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c, d, q;\n"
      "  always_latch\n"
      "    if (a)\n"
      "      q <= 4'h1;\n"
      "    else if (b)\n"
      "      q <= 4'h2;\n"
      "    else if (c)\n"
      "      q <= 4'h3;\n"
      "    else\n"
      "      q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  auto* top_if = item->body;
  ASSERT_NE(top_if, nullptr);
  EXPECT_EQ(top_if->kind, StmtKind::kIf);
  // First else branch is an if.
  ASSERT_NE(top_if->else_branch, nullptr);
  EXPECT_EQ(top_if->else_branch->kind, StmtKind::kIf);
  // Second else branch is also an if.
  auto* mid_if = top_if->else_branch;
  ASSERT_NE(mid_if->else_branch, nullptr);
  EXPECT_EQ(mid_if->else_branch->kind, StmtKind::kIf);
  // Terminal else is a plain assignment.
  auto* inner_if = mid_if->else_branch;
  ASSERT_NE(inner_if->else_branch, nullptr);
  EXPECT_EQ(inner_if->else_branch->kind, StmtKind::kNonblockingAssign);
}

// ---------------------------------------------------------------------------
// 28. always_latch with system function call in body.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_SystemFunctionCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic en;\n"
              "  logic [7:0] q, d;\n"
              "  always_latch begin\n"
              "    if (en) begin\n"
              "      q <= d;\n"
              "      $display(\"latch update\");\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}

// ---------------------------------------------------------------------------
// 29. Case with begin-end blocks in items inside always_latch.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_CaseWithBeginEndItems) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] q, a, b;\n"
      "  always_latch\n"
      "    case (sel)\n"
      "      2'b00: begin\n"
      "        q <= a;\n"
      "      end\n"
      "      2'b01: begin\n"
      "        q <= b;\n"
      "      end\n"
      "      default: begin\n"
      "        q <= q;\n"
      "      end\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  ASSERT_GE(item->body->case_items.size(), 3u);
  for (const auto& ci : item->body->case_items) {
    ASSERT_NE(ci.body, nullptr);
    EXPECT_EQ(ci.body->kind, StmtKind::kBlock);
  }
}

}  // namespace
