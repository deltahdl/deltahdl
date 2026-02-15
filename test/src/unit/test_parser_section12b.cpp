#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult12b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult12b Parse(const std::string& src) {
  ParseResult12b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static Stmt* FirstInitialStmt(ParseResult12b& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

// =============================================================================
// LRM section 12.4 -- Conditional if-else statement
// =============================================================================

// Basic if without else -- verifies condition/branch pointers.
TEST(ParserSection12, IfNoElseConditionAndBranches) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->else_branch, nullptr);
}

// If-else with both branches.
TEST(ParserSection12, IfWithElse) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "    else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);
}

// Chained if-else-if-else produces nested kIf on else_branch.
TEST(ParserSection12, IfElseIfElseChain) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a == 0) x = 0;\n"
      "    else if (a == 1) x = 1;\n"
      "    else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  EXPECT_NE(stmt->else_branch->else_branch, nullptr);
}

// If with begin-end block body (then-only).
TEST(ParserSection12, IfBlockBodyThenOnly) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) begin\n"
      "      x = 1;\n"
      "      y = 2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
}

// =============================================================================
// LRM section 12.4.2 -- unique-if, unique0-if, priority-if (additional cases)
// =============================================================================

// unique if with else-if chain and no final else (LRM says violation).
TEST(ParserSection12, UniqueIfChainNoElse) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    unique if (a == 0) x = 0;\n"
      "    else if (a == 1) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->else_branch->else_branch, nullptr);
}

// unique0 if with else-if chain (no violation when none match).
TEST(ParserSection12, Unique0IfChainElseIf) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    unique0 if (a == 0) x = 0;\n"
      "    else if (a == 1) x = 1;\n"
      "    else if (a == 2) x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
}

// priority if with a final else (covers all cases, LRM says no violation).
TEST(ParserSection12, PriorityIfWithElse) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    priority if (a[2:1] == 0) x = 0;\n"
      "    else if (a[2] == 0) x = 1;\n"
      "    else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
  // Verify the else-if chain is fully linked.
  ASSERT_NE(stmt->else_branch, nullptr);
  ASSERT_NE(stmt->else_branch->else_branch, nullptr);
}

// Plain if (no qualifier) has kNone qualifier.
TEST(ParserSection12, PlainIfHasNoQualifier) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "    else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kNone);
}

// =============================================================================
// LRM section 12.5 -- Case statement (additional cases)
// =============================================================================

// Case with multiple expressions in a single item (comma-separated).
TEST(ParserSection12, CaseMultipleExprsPerItem) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      0, 1: x = 1;\n"
      "      2, 3: x = 2;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_GE(stmt->case_items.size(), 3u);
  // First item has two patterns (0, 1).
  EXPECT_EQ(stmt->case_items[0].patterns.size(), 2u);
}

// Case with only default item.
TEST(ParserSection12, CaseWithOnlyDefault) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_EQ(stmt->case_items.size(), 1u);
  EXPECT_TRUE(stmt->case_items[0].is_default);
}

// Case with block body in an item.
TEST(ParserSection12, CaseItemWithBlock) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      0: begin\n"
      "        x = 1;\n"
      "        y = 2;\n"
      "      end\n"
      "      1: x = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_GE(stmt->case_items.size(), 2u);
  ASSERT_NE(stmt->case_items[0].body, nullptr);
  EXPECT_EQ(stmt->case_items[0].body->kind, StmtKind::kBlock);
}

// =============================================================================
// LRM section 12.5.1 -- casex / casez (additional cases)
// =============================================================================

// casez with wildcard question-mark pattern.
TEST(ParserSection12, CasezWithQuestionMark) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    casez (ir)\n"
      "      8'b1???????: x = 1;\n"
      "      8'b01??????: x = 2;\n"
      "      8'b00010???: x = 3;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
  ASSERT_EQ(stmt->case_items.size(), 4u);
}

// casex with multiple case items and expressions.
TEST(ParserSection12, CasexMultipleItemsWithExpressions) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    casex (data)\n"
      "      8'b001100xx: x = 1;\n"
      "      8'b1100xx00: x = 2;\n"
      "      8'b00xx0011: x = 3;\n"
      "      8'bxx010100: x = 4;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasex);
  ASSERT_EQ(stmt->case_items.size(), 4u);
}

// unique casez combines qualifier with casez keyword.
TEST(ParserSection12, UniqueCasezQualifier) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    unique casez (sel)\n"
      "      2'b1?: x = 1;\n"
      "      2'b01: x = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasez);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
}

// priority casex.
TEST(ParserSection12, PriorityCasex) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    priority casex (sel)\n"
      "      2'b1?: x = 1;\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->case_kind, TokenKind::kKwCasex);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

// =============================================================================
// LRM section 12.7 -- Loop statements (additional cases)
// =============================================================================

// Repeat loop with expression (not just a literal).
TEST(ParserSection12, RepeatWithExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    repeat (n + 1) begin\n"
      "      x = x + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRepeat);
  EXPECT_NE(stmt->condition, nullptr);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

// Forever loop wrapping a timing control.
TEST(ParserSection12, ForeverWithTimingControl) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial begin\n"
      "    forever begin\n"
      "      @(posedge clk);\n"
      "      x = ~x;\n"
      "    end\n"
      "  end\n"
      "endmodule\n"));
}

// Nested loops: for inside while.
TEST(ParserSection12, NestedForInsideWhile) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    while (running) begin\n"
      "      for (int i = 0; i < 8; i = i + 1)\n"
      "        data[i] = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
  ASSERT_GE(stmt->body->stmts.size(), 1u);
  EXPECT_EQ(stmt->body->stmts[0]->kind, StmtKind::kFor);
}

// =============================================================================
// LRM section 12.7.1 -- For loop with variable declarations (additional cases)
// =============================================================================

// For loop with multiple init assignments (comma-separated).
TEST(ParserSection12, ForWithMultipleInits) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0, j = 10; i < j; i = i + 1)\n"
      "      x = i;\n"
      "  end\n"
      "endmodule\n"));
}

// For loop with increment expression in step.
TEST(ParserSection12, ForWithIncrementStep) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++)\n"
      "      x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_step, nullptr);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kInt);
}

// For loop with byte variable declaration.
TEST(ParserSection12, ForWithByteDecl) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (byte b = 0; b < 100; b = b + 1)\n"
      "      data = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kByte);
}

// For loop with block body.
TEST(ParserSection12, ForWithBlockBody) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 4; i = i + 1) begin\n"
      "      a[i] = i;\n"
      "      b[i] = i * 2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_NE(stmt->for_body, nullptr);
  EXPECT_EQ(stmt->for_body->kind, StmtKind::kBlock);
}

// =============================================================================
// LRM section 12.8 -- Jump statements (additional cases)
// =============================================================================

// Return with complex expression.
TEST(ParserSection12, ReturnWithComplexExpr) {
  auto r = Parse(
      "module t;\n"
      "  function int compute(int a, int b);\n"
      "    return a * b + 1;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  Stmt* ret = nullptr;
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kFunctionDecl) continue;
    for (auto* s : item->func_body_stmts) {
      if (s->kind == StmtKind::kReturn) ret = s;
    }
  }
  ASSERT_NE(ret, nullptr);
  EXPECT_EQ(ret->kind, StmtKind::kReturn);
  ASSERT_NE(ret->expr, nullptr);
  // The expression is a binary op (a * b + 1).
  EXPECT_EQ(ret->expr->kind, ExprKind::kBinary);
}

// Break inside while loop.
TEST(ParserSection12, BreakInsideWhile) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    while (1) begin\n"
      "      if (done) break;\n"
      "      x = x + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
  auto* blk = stmt->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_GE(blk->stmts.size(), 1u);
  auto* if_stmt = blk->stmts[0];
  EXPECT_EQ(if_stmt->kind, StmtKind::kIf);
  ASSERT_NE(if_stmt->then_branch, nullptr);
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kBreak);
}

// Continue inside do-while loop.
TEST(ParserSection12, ContinueInsideDoWhile) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    do begin\n"
      "      if (skip) continue;\n"
      "      x = x + 1;\n"
      "    end while (x < 10);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  auto* blk = stmt->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_GE(blk->stmts.size(), 1u);
  auto* if_stmt = blk->stmts[0];
  EXPECT_EQ(if_stmt->kind, StmtKind::kIf);
  ASSERT_NE(if_stmt->then_branch, nullptr);
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kContinue);
}

// Break inside foreach loop (LRM 12.8: break jumps out of entire loop).
TEST(ParserSection12, BreakInsideForeach) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    foreach (arr[i]) begin\n"
      "      if (arr[i] == 0) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  auto* blk = stmt->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_GE(blk->stmts.size(), 1u);
  EXPECT_EQ(blk->stmts[0]->kind, StmtKind::kIf);
  EXPECT_EQ(blk->stmts[0]->then_branch->kind, StmtKind::kBreak);
}

// Continue inside foreach loop.
TEST(ParserSection12, ContinueInsideForeach) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    foreach (arr[i]) begin\n"
      "      if (arr[i] == 0) continue;\n"
      "      sum = sum + arr[i];\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  auto* blk = stmt->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_GE(blk->stmts.size(), 2u);
  auto* if_stmt = blk->stmts[0];
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kContinue);
}

// Return from void function (task-like usage).
TEST(ParserSection12, ReturnFromVoidFunctionEarly) {
  auto r = Parse(
      "module t;\n"
      "  function void check(int val);\n"
      "    if (val < 0) return;\n"
      "    $display(\"ok\");\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* fn = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl && item->name == "check") {
      fn = item;
    }
  }
  ASSERT_NE(fn, nullptr);
  ASSERT_GE(fn->func_body_stmts.size(), 1u);
  // First statement is an if whose then_branch is a return.
  auto* if_stmt = fn->func_body_stmts[0];
  EXPECT_EQ(if_stmt->kind, StmtKind::kIf);
  ASSERT_NE(if_stmt->then_branch, nullptr);
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kReturn);
  EXPECT_EQ(if_stmt->then_branch->expr, nullptr);
}

// =============================================================================
// Combined patterns -- real-world usage patterns from sections 12.4-12.8
// =============================================================================

// Case inside always_comb with unique qualifier.
TEST(ParserSection12, UniqueCaseInsideAlwaysComb) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] out;\n"
      "  always_comb begin\n"
      "    unique case (sel)\n"
      "      2'd0: out = 8'hAA;\n"
      "      2'd1: out = 8'hBB;\n"
      "      2'd2: out = 8'hCC;\n"
      "      2'd3: out = 8'hDD;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n"));
}

// If-else inside for loop body.
TEST(ParserSection12, IfElseInsideForBody) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 16; i = i + 1) begin\n"
      "      if (i[0]) odd[i] = 1;\n"
      "      else even[i] = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_NE(stmt->for_body, nullptr);
  EXPECT_EQ(stmt->for_body->kind, StmtKind::kBlock);
  ASSERT_GE(stmt->for_body->stmts.size(), 1u);
  EXPECT_EQ(stmt->for_body->stmts[0]->kind, StmtKind::kIf);
}

// Case inside a for loop.
TEST(ParserSection12, CaseInsideForLoop) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 4; i = i + 1) begin\n"
      "      case (mode)\n"
      "        0: data[i] = 0;\n"
      "        1: data[i] = i;\n"
      "        default: data[i] = 8'hFF;\n"
      "      endcase\n"
      "    end\n"
      "  end\n"
      "endmodule\n"));
}

// Unique0 case with empty default.
TEST(ParserSection12, Unique0CaseWithDefault) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    unique0 case (sel)\n"
      "      0: x = 1;\n"
      "      1: x = 2;\n"
      "      default: ;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique0);
  ASSERT_GE(stmt->case_items.size(), 3u);
  EXPECT_TRUE(stmt->case_items[2].is_default);
}

// Case statement where the expression is checked.
TEST(ParserSection12, CaseStatementExprIsNotNull) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (a + b)\n"
      "      0: x = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_NE(stmt->expr, nullptr);
}

// Casez inside always_ff.
TEST(ParserSection12, CasezInsideAlwaysFF) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  logic clk;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] q;\n"
      "  always_ff @(posedge clk) begin\n"
      "    casez (sel)\n"
      "      2'b1?: q <= 4'd1;\n"
      "      2'b01: q <= 4'd2;\n"
      "      default: q <= 4'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n"));
}

// While loop with null body (semicolon).
TEST(ParserSection12, WhileWithNullBody) {
  EXPECT_TRUE(ParseOk(
      "module t;\n"
      "  initial begin\n"
      "    while (0) ;\n"
      "  end\n"
      "endmodule\n"));
}

// Multiple case items without default.
TEST(ParserSection12, CaseNoDefault) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      0: x = 1;\n"
      "      1: x = 2;\n"
      "      2: x = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_EQ(stmt->case_items.size(), 3u);
  for (const auto& item : stmt->case_items) {
    EXPECT_FALSE(item.is_default);
  }
}

// For loop with decrement.
TEST(ParserSection12, ForWithDecrement) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 9; i >= 0; i--)\n"
      "      x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->for_init_type.kind, DataTypeKind::kInt);
  EXPECT_NE(stmt->for_step, nullptr);
}

// Do-while with complex condition.
TEST(ParserSection12, DoWhileComplexCondition) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    do begin\n"
      "      x = x + 1;\n"
      "    end while (x < 10 && !done);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  EXPECT_NE(stmt->condition, nullptr);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}
