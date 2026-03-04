// §9.2.2.3: Latched logic always_latch procedure

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserA602, AlwaysConstruct_AlwaysLatch) {
  auto r = Parse(
      "module m;\n"
      "  always_latch\n"
      "    if (en) q = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
}
// ---------------------------------------------------------------------------
// 30. Three always_latch blocks in same module, counting them all.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_ThreeAlwaysLatchBlocks) {
  auto r = Parse(
      "module m;\n"
      "  logic en, d1, d2, d3, q1, q2, q3;\n"
      "  always_latch\n"
      "    if (en) q1 <= d1;\n"
      "  always_latch\n"
      "    if (en) q2 <= d2;\n"
      "  always_latch\n"
      "    if (en) q3 <= d3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      ++count;
      EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
      EXPECT_TRUE(item->sensitivity.empty());
      ASSERT_NE(item->body, nullptr);
      EXPECT_EQ(item->body->kind, StmtKind::kIf);
    }
  }
  EXPECT_EQ(count, 3);
}
static ModuleItem* FirstAlwaysLatchItem(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysLatchBlock) return item;
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
// =============================================================================
// §4.6: always_latch with if (no else)
// =============================================================================
TEST(ParserSection4, Sec4_6_AlwaysLatchIfNoElse) {
  auto r = Parse(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch\n"
      "    if (en) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kIf);
  EXPECT_EQ(item->body->else_branch, nullptr);
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
// =============================================================================
// §9.2.2.4 -- always_ff procedure
// =============================================================================
TEST(ParserSection9b, AlwaysLatchMultipleOutputs) {
  auto r = Parse(
      "module m;\n"
      "  always_latch begin\n"
      "    if (en) begin\n"
      "      q1 <= d1;\n"
      "      q2 <= d2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
// Returns the first always_* item from the first module.
// ---------------------------------------------------------------------------
// 21. always_latch block
// ---------------------------------------------------------------------------
TEST(ParserSection4, Sec4_5_AlwaysLatch) {
  auto r = Parse(
      "module m;\n"
      "  reg q, d, en;\n"
      "  always_latch\n"
      "    if (en) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
  ASSERT_NE(item->body, nullptr);
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

static ModuleItem* NthAlwaysLatchItem(ParseResult& r, size_t n) {
  size_t count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      if (count == n) return item;
      ++count;
    }
  }
  return nullptr;
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
// =============================================================================
// LRM section 9.2.2.3 -- always_latch procedure
// Latched logic behavior modeled with always_latch.
// =============================================================================
TEST(ParserSection9c, AlwaysLatchWithBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  logic ck, d, q;\n"
      "  always_latch begin\n"
      "    if (ck) q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
}
TEST(ParserSection9, AlwaysLatch) {
  auto r = Parse(
      "module m;\n"
      "  always_latch\n"
      "    if (en) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
  ASSERT_NE(item->body, nullptr);
}

// =============================================================================
// §4.6: always_latch guarantees latch semantics
// =============================================================================
TEST(ParserSection4, Sec4_6_AlwaysLatchLatch) {
  auto r = Parse(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch begin\n"
      "    if (en) q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
  ASSERT_NE(item->body, nullptr);
}

}  // namespace
