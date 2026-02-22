#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult10b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult10b Parse(const std::string &src) {
  ParseResult10b result;
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

static Stmt *FirstInitialStmt(ParseResult10b &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock)
      continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static Stmt *NthInitialStmt(ParseResult10b &r, size_t n) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock)
      continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      if (n < item->body->stmts.size())
        return item->body->stmts[n];
    }
  }
  return nullptr;
}

// =============================================================================
// LRM section 10.6.1 -- The assign and deassign procedural statements
// =============================================================================

// --- 1. Basic assign in initial block ---
TEST(ParserSection10, Sec10_6_1_AssignInInitialBlock) {
  auto r = Parse("module m;\n"
                 "  reg q;\n"
                 "  initial begin\n"
                 "    assign q = 0;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "q");
  ASSERT_NE(stmt->rhs, nullptr);
}

// --- 2. Basic deassign in initial block ---
TEST(ParserSection10, Sec10_6_1_DeassignInInitialBlock) {
  auto r = Parse("module m;\n"
                 "  reg q;\n"
                 "  initial begin\n"
                 "    deassign q;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDeassign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "q");
  EXPECT_EQ(stmt->rhs, nullptr);
}

// --- 3. Assign with expression RHS (a + b) ---
TEST(ParserSection10, Sec10_6_1_AssignExpressionRhs) {
  auto r = Parse("module m;\n"
                 "  reg [7:0] a, b, c;\n"
                 "  initial begin\n"
                 "    assign c = a + b;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
}

// --- 4. Assign with concatenation RHS ---
TEST(ParserSection10, Sec10_6_1_AssignConcatenationRhs) {
  auto r = Parse("module m;\n"
                 "  reg [3:0] out;\n"
                 "  reg a, b, c, d;\n"
                 "  initial begin\n"
                 "    assign out = {a, b, c, d};\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
}

// --- 5. Assign to bit-select ---
TEST(ParserSection10, Sec10_6_1_AssignBitSelect) {
  auto r = Parse("module m;\n"
                 "  reg [7:0] data;\n"
                 "  initial begin\n"
                 "    assign data[3] = 1'b1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->rhs, nullptr);
}

// --- 6. Assign to part-select ---
TEST(ParserSection10, Sec10_6_1_AssignPartSelect) {
  auto r = Parse("module m;\n"
                 "  reg [7:0] data;\n"
                 "  initial begin\n"
                 "    assign data[3:0] = 4'hA;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->rhs, nullptr);
}

// --- 7. Assign to concatenation LHS (new pattern: three regs) ---
TEST(ParserSection10, Sec10_6_1_AssignConcatLhsThreeRegs) {
  auto r = Parse("module m;\n"
                 "  reg a, b, c;\n"
                 "  initial begin\n"
                 "    assign {a, b, c} = 3'b101;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->lhs->elements.size(), 3u);
}

// --- 8. Deassign concatenation LHS (three regs) ---
TEST(ParserSection10, Sec10_6_1_DeassignConcatLhsThreeRegs) {
  auto r = Parse("module m;\n"
                 "  reg a, b, c;\n"
                 "  initial begin\n"
                 "    deassign {a, b, c};\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDeassign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->lhs->elements.size(), 3u);
}

// --- 9. Assign in if-else branch ---
TEST(ParserSection10, Sec10_6_1_AssignInIfElse) {
  auto r = Parse("module m;\n"
                 "  reg q, sel;\n"
                 "  initial begin\n"
                 "    if (sel)\n"
                 "      assign q = 1;\n"
                 "    else\n"
                 "      assign q = 0;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kAssign);
}

// --- 10. Assign in case statement ---
TEST(ParserSection10, Sec10_6_1_AssignInCase) {
  auto r = Parse("module m;\n"
                 "  reg [1:0] sel;\n"
                 "  reg q;\n"
                 "  initial begin\n"
                 "    case (sel)\n"
                 "      2'b00: assign q = 0;\n"
                 "      2'b01: assign q = 1;\n"
                 "      default: deassign q;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_GE(stmt->case_items.size(), 3u);
  EXPECT_EQ(stmt->case_items[0].body->kind, StmtKind::kAssign);
  EXPECT_EQ(stmt->case_items[1].body->kind, StmtKind::kAssign);
  EXPECT_EQ(stmt->case_items[2].body->kind, StmtKind::kDeassign);
}

// --- 11. Assign in always block with event control ---
TEST(ParserSection10, Sec10_6_1_AssignInAlwaysWithEvent) {
  auto r = Parse("module m;\n"
                 "  reg q, clear;\n"
                 "  always @(clear)\n"
                 "    if (!clear) assign q = 0;\n"
                 "    else deassign q;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *mod = r.cu->modules[0];
  // Find the always block.
  ModuleItem *always_item = nullptr;
  for (auto *item : mod->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) {
      always_item = item;
      break;
    }
  }
  ASSERT_NE(always_item, nullptr);
  ASSERT_NE(always_item->body, nullptr);
}

// --- 12. Multiple assigns to different vars in same block ---
TEST(ParserSection10, Sec10_6_1_MultipleAssignsDifferentVars) {
  auto r = Parse("module m;\n"
                 "  reg a, b, c;\n"
                 "  initial begin\n"
                 "    assign a = 1;\n"
                 "    assign b = 0;\n"
                 "    assign c = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *s0 = NthInitialStmt(r, 0);
  auto *s1 = NthInitialStmt(r, 1);
  auto *s2 = NthInitialStmt(r, 2);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  ASSERT_NE(s2, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kAssign);
  EXPECT_EQ(s1->kind, StmtKind::kAssign);
  EXPECT_EQ(s2->kind, StmtKind::kAssign);
  EXPECT_EQ(s0->lhs->text, "a");
  EXPECT_EQ(s1->lhs->text, "b");
  EXPECT_EQ(s2->lhs->text, "c");
}

// --- 13. Deassign then normal procedural assign ---
TEST(ParserSection10, Sec10_6_1_DeassignThenProceduralAssign) {
  auto r = Parse("module m;\n"
                 "  reg q;\n"
                 "  initial begin\n"
                 "    deassign q;\n"
                 "    q = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *s0 = NthInitialStmt(r, 0);
  auto *s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kDeassign);
  EXPECT_EQ(s1->kind, StmtKind::kBlockingAssign);
}

// --- 14. Assign with ternary expression RHS ---
TEST(ParserSection10, Sec10_6_1_AssignTernaryRhs) {
  auto r = Parse("module m;\n"
                 "  reg q, sel, a, b;\n"
                 "  initial begin\n"
                 "    assign q = sel ? a : b;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
}

// --- 15. Assign with function call RHS ---
TEST(ParserSection10, Sec10_6_1_AssignFunctionCallRhs) {
  auto r = Parse("module m;\n"
                 "  reg [7:0] q;\n"
                 "  initial begin\n"
                 "    assign q = compute(a, b);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

// --- 16. Assign with unary operator RHS ---
TEST(ParserSection10, Sec10_6_1_AssignUnaryRhs) {
  auto r = Parse("module m;\n"
                 "  reg a, q;\n"
                 "  initial begin\n"
                 "    assign q = ~a;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kUnary);
}

// --- 17. Assign inside for loop ---
TEST(ParserSection10, Sec10_6_1_AssignInsideForLoop) {
  auto r = Parse("module m;\n"
                 "  reg [3:0] q;\n"
                 "  initial begin\n"
                 "    for (int i = 0; i < 4; i++)\n"
                 "      assign q[i] = 1'b0;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  ASSERT_NE(stmt->for_body, nullptr);
  EXPECT_EQ(stmt->for_body->kind, StmtKind::kAssign);
}

// --- 18. D-FF with clear/preset pattern (LRM example) ---
TEST(ParserSection10, Sec10_6_1_DFlipFlopClearPreset) {
  EXPECT_TRUE(
      ParseOk("module dff_cp(output reg q, input d, clear, preset, clock);\n"
              "  always @(clear or preset)\n"
              "    if (!clear)\n"
              "      assign q = 0;\n"
              "    else if (!preset)\n"
              "      assign q = 1;\n"
              "    else\n"
              "      deassign q;\n"
              "  always @(posedge clock)\n"
              "    q <= d;\n"
              "endmodule\n"));
}

// --- 19. Assign in named block ---
TEST(ParserSection10, Sec10_6_1_AssignInNamedBlock) {
  auto r = Parse("module m;\n"
                 "  reg q;\n"
                 "  initial begin : my_block\n"
                 "    assign q = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
}

// --- 20. Assign in fork-join ---
TEST(ParserSection10, Sec10_6_1_AssignInForkJoin) {
  auto r = Parse("module m;\n"
                 "  reg a, b;\n"
                 "  initial begin\n"
                 "    fork\n"
                 "      assign a = 1;\n"
                 "      assign b = 0;\n"
                 "    join\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kAssign);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kAssign);
}

// --- 21. Assign with system function RHS ---
TEST(ParserSection10, Sec10_6_1_AssignSystemFuncRhs) {
  auto r = Parse("module m;\n"
                 "  reg [31:0] q;\n"
                 "  initial begin\n"
                 "    assign q = $random;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
}

// --- 22. Multiple sequential assigns to same variable ---
TEST(ParserSection10, Sec10_6_1_MultipleAssignsSameVar) {
  auto r = Parse("module m;\n"
                 "  reg q;\n"
                 "  initial begin\n"
                 "    assign q = 0;\n"
                 "    assign q = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *s0 = NthInitialStmt(r, 0);
  auto *s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kAssign);
  EXPECT_EQ(s1->kind, StmtKind::kAssign);
  EXPECT_EQ(s0->lhs->text, "q");
  EXPECT_EQ(s1->lhs->text, "q");
}

// --- 23. Deassign multiple variables in sequence ---
TEST(ParserSection10, Sec10_6_1_DeassignMultipleVars) {
  auto r = Parse("module m;\n"
                 "  reg a, b, c;\n"
                 "  initial begin\n"
                 "    deassign a;\n"
                 "    deassign b;\n"
                 "    deassign c;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *s0 = NthInitialStmt(r, 0);
  auto *s1 = NthInitialStmt(r, 1);
  auto *s2 = NthInitialStmt(r, 2);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  ASSERT_NE(s2, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kDeassign);
  EXPECT_EQ(s1->kind, StmtKind::kDeassign);
  EXPECT_EQ(s2->kind, StmtKind::kDeassign);
  EXPECT_EQ(s0->lhs->text, "a");
  EXPECT_EQ(s1->lhs->text, "b");
  EXPECT_EQ(s2->lhs->text, "c");
}

// --- 24. Assign with delay before it ---
TEST(ParserSection10, Sec10_6_1_DelayBeforeAssign) {
  auto r = Parse("module m;\n"
                 "  reg q;\n"
                 "  initial begin\n"
                 "    #10 assign q = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- 25. Assign inside nested if-else ---
TEST(ParserSection10, Sec10_6_1_AssignNestedIfElse) {
  auto r = Parse("module m;\n"
                 "  reg q, a, b;\n"
                 "  initial begin\n"
                 "    if (a)\n"
                 "      if (b)\n"
                 "        assign q = 1;\n"
                 "      else\n"
                 "        assign q = 0;\n"
                 "    else\n"
                 "      deassign q;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  // Outer then-branch is another if.
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kIf);
  // Inner then/else are both assigns.
  EXPECT_EQ(stmt->then_branch->then_branch->kind, StmtKind::kAssign);
  EXPECT_EQ(stmt->then_branch->else_branch->kind, StmtKind::kAssign);
  // Outer else-branch is deassign.
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kDeassign);
}

// --- 26. Assign with reduction operator RHS ---
TEST(ParserSection10, Sec10_6_1_AssignReductionRhs) {
  auto r = Parse("module m;\n"
                 "  reg [7:0] data;\n"
                 "  reg parity;\n"
                 "  initial begin\n"
                 "    assign parity = ^data;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kUnary);
}

// --- 27. Assign to vector variable ---
TEST(ParserSection10, Sec10_6_1_AssignToVector) {
  auto r = Parse("module m;\n"
                 "  reg [15:0] vec;\n"
                 "  initial begin\n"
                 "    assign vec = 16'hDEAD;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "vec");
  ASSERT_NE(stmt->rhs, nullptr);
}

// --- 28. Assign in task body ---
TEST(ParserSection10, Sec10_6_1_AssignInTaskBody) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  reg q;\n"
                      "  task set_q;\n"
                      "    assign q = 1;\n"
                      "  endtask\n"
                      "  task clear_q;\n"
                      "    deassign q;\n"
                      "  endtask\n"
                      "endmodule\n"));
}

// --- 29. Assign/deassign interleaved with nonblocking assigns ---
TEST(ParserSection10, Sec10_6_1_InterleavedWithNonblocking) {
  auto r = Parse("module m;\n"
                 "  reg q, d;\n"
                 "  initial begin\n"
                 "    assign q = 1;\n"
                 "    q <= 0;\n"
                 "    deassign q;\n"
                 "    q <= d;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *s0 = NthInitialStmt(r, 0);
  auto *s1 = NthInitialStmt(r, 1);
  auto *s2 = NthInitialStmt(r, 2);
  auto *s3 = NthInitialStmt(r, 3);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  ASSERT_NE(s2, nullptr);
  ASSERT_NE(s3, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kAssign);
  EXPECT_EQ(s1->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(s2->kind, StmtKind::kDeassign);
  EXPECT_EQ(s3->kind, StmtKind::kNonblockingAssign);
}

// --- 30. Full D-FF with assign/deassign and always @(posedge) ---
TEST(ParserSection10, Sec10_6_1_FullDFlipFlopPattern) {
  auto r = Parse("module dff_full(output reg q, input d, clr, pre, clk);\n"
                 "  always @(clr or pre) begin\n"
                 "    if (!clr)\n"
                 "      assign q = 0;\n"
                 "    else if (!pre)\n"
                 "      assign q = 1;\n"
                 "    else\n"
                 "      deassign q;\n"
                 "  end\n"
                 "  always @(posedge clk)\n"
                 "    q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "dff_full");
  // Should have at least two always blocks.
  int always_count = 0;
  for (auto *item : mod->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock)
      always_count++;
  }
  EXPECT_GE(always_count, 2);
}
