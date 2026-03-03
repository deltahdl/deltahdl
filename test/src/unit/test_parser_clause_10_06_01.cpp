// §10.6.1: The assign and deassign procedural statements

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// Return all statements from the first initial block's begin/end.
static std::vector<Stmt*> AllInitialStmts(ParseResult& r) {
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  if (!item || !item->body) return {};
  if (item->body->kind == StmtKind::kBlock) return item->body->stmts;
  return {item->body};
}

namespace {

// =============================================================================
// A.6.2 Production: procedural_continuous_assignment
// procedural_continuous_assignment ::=
//   assign variable_assignment
//   | deassign variable_lvalue
//   | force variable_assignment
//   | force net_assignment
//   | release variable_lvalue
//   | release net_lvalue
// =============================================================================
TEST(ParserA602, ProceduralAssign_Basic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin assign q = d; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(ParserA602, ProceduralDeassign_Basic) {
  auto r = Parse(
      "module m;\n"
      "  initial begin deassign q; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDeassign);
  EXPECT_NE(stmt->lhs, nullptr);
}

TEST(ParserA602, ProceduralAssign_WithBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  initial begin assign q[0] = d; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

// --- 28. Assign in task body ---
TEST(ParserSection10, Sec10_6_1_AssignInTaskBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  reg q;\n"
              "  task set_q;\n"
              "    assign q = 1;\n"
              "  endtask\n"
              "  task clear_q;\n"
              "    deassign q;\n"
              "  endtask\n"
              "endmodule\n"));
}

// Helper: extract 4 initial statements and verify non-null.
struct FourStmts {
  Stmt* s0;
  Stmt* s1;
  Stmt* s2;
  Stmt* s3;
};

static FourStmts Get4InitialStmts(auto& r) {
  FourStmts fs;
  fs.s0 = NthInitialStmt(r, 0);
  fs.s1 = NthInitialStmt(r, 1);
  fs.s2 = NthInitialStmt(r, 2);
  fs.s3 = NthInitialStmt(r, 3);
  EXPECT_NE(fs.s0, nullptr);
  EXPECT_NE(fs.s1, nullptr);
  EXPECT_NE(fs.s2, nullptr);
  EXPECT_NE(fs.s3, nullptr);
  return fs;
}

struct ParseResult10d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult10d Parse(const std::string& src) {
  ParseResult10d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* NthInitialStmt(ParseResult10d& r, size_t n) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      if (n < item->body->stmts.size()) return item->body->stmts[n];
    }
  }
  return nullptr;
}

// --- 29. Assign/deassign interleaved with nonblocking assigns ---
TEST(ParserSection10, Sec10_6_1_InterleavedWithNonblocking) {
  auto r = Parse(
      "module m;\n"
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
  auto [s0, s1, s2, s3] = Get4InitialStmts(r);
  EXPECT_EQ(s0->kind, StmtKind::kAssign);
  EXPECT_EQ(s1->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(s2->kind, StmtKind::kDeassign);
  EXPECT_EQ(s3->kind, StmtKind::kNonblockingAssign);
}

// --- 30. Full D-FF with assign/deassign and always @(posedge) ---
TEST(ParserSection10, Sec10_6_1_FullDFlipFlopPattern) {
  auto r = Parse(
      "module dff_full(output reg q, input d, clr, pre, clk);\n"
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
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "dff_full");
  // Should have at least two always blocks.
  int always_count = 0;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) always_count++;
  }
  EXPECT_GE(always_count, 2);
}

struct ParseResult10b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult10b Parse(const std::string& src) {
  ParseResult10b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM section 10.6.1 -- Assign/deassign additional patterns
// =============================================================================
TEST(ParserSection10, AssignInAlwaysBlock) {
  // LRM example: D-type flip-flop with clear/preset using assign/deassign.
  auto r = Parse(
      "module dff(output q, input d, clear, preset, clock);\n"
      "  logic q;\n"
      "  always @(clear or preset)\n"
      "    if (!clear) assign q = 0;\n"
      "    else if (!preset) assign q = 1;\n"
      "    else deassign q;\n"
      "  always @(posedge clock) q = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "dff");
}

static Stmt* FirstInitialStmt(ParseResult10b& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

TEST(ParserSection10, AssignConcatLhs) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    assign {a, b} = 2'b10;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
}

// =============================================================================
// LRM section 10.6.1 -- The assign and deassign procedural statements
// =============================================================================
// --- 1. Basic assign in initial block ---
TEST(ParserSection10, Sec10_6_1_AssignInInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    assign q = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "q");
  ASSERT_NE(stmt->rhs, nullptr);
}

// --- 2. Basic deassign in initial block ---
TEST(ParserSection10, Sec10_6_1_DeassignInInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    deassign q;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDeassign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->text, "q");
  EXPECT_EQ(stmt->rhs, nullptr);
}

// --- 3. Assign with expression RHS (a + b) ---
TEST(ParserSection10, Sec10_6_1_AssignExpressionRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] a, b, c;\n"
      "  initial begin\n"
      "    assign c = a + b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
}

// --- 4. Assign with concatenation RHS ---
TEST(ParserSection10, Sec10_6_1_AssignConcatenationRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [3:0] out;\n"
      "  reg a, b, c, d;\n"
      "  initial begin\n"
      "    assign out = {a, b, c, d};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
}

// --- 5. Assign to bit-select ---
TEST(ParserSection10, Sec10_6_1_AssignBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] data;\n"
      "  initial begin\n"
      "    assign data[3] = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->rhs, nullptr);
}

// --- 6. Assign to part-select ---
TEST(ParserSection10, Sec10_6_1_AssignPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] data;\n"
      "  initial begin\n"
      "    assign data[3:0] = 4'hA;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->rhs, nullptr);
}

// --- 7. Assign to concatenation LHS (new pattern: three regs) ---
TEST(ParserSection10, Sec10_6_1_AssignConcatLhsThreeRegs) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c;\n"
      "  initial begin\n"
      "    assign {a, b, c} = 3'b101;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->lhs->elements.size(), 3u);
}

// --- 8. Deassign concatenation LHS (three regs) ---
TEST(ParserSection10, Sec10_6_1_DeassignConcatLhsThreeRegs) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c;\n"
      "  initial begin\n"
      "    deassign {a, b, c};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDeassign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->lhs->elements.size(), 3u);
}

// --- 9. Assign in if-else branch ---
TEST(ParserSection10, Sec10_6_1_AssignInIfElse) {
  auto r = Parse(
      "module m;\n"
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kAssign);
}

// --- 10. Assign in case statement ---
TEST(ParserSection10, Sec10_6_1_AssignInCase) {
  auto r = Parse(
      "module m;\n"
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_GE(stmt->case_items.size(), 3u);
  EXPECT_EQ(stmt->case_items[0].body->kind, StmtKind::kAssign);
  EXPECT_EQ(stmt->case_items[1].body->kind, StmtKind::kAssign);
  EXPECT_EQ(stmt->case_items[2].body->kind, StmtKind::kDeassign);
}

// §10.6.1: procedural_continuous_assignment (assign)
TEST(ParserA604, StmtItemProceduralContinuousAssignment) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assign x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
}

// --- 11. Assign in always block with event control ---
TEST(ParserSection10, Sec10_6_1_AssignInAlwaysWithEvent) {
  auto r = Parse(
      "module m;\n"
      "  reg q, clear;\n"
      "  always @(clear)\n"
      "    if (!clear) assign q = 0;\n"
      "    else deassign q;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  // Find the always block.
  ModuleItem* always_item = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) {
      always_item = item;
      break;
    }
  }
  ASSERT_NE(always_item, nullptr);
  ASSERT_NE(always_item->body, nullptr);
}

static Stmt* NthInitialStmt(ParseResult10b& r, size_t n) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      if (n < item->body->stmts.size()) return item->body->stmts[n];
    }
  }
  return nullptr;
}

// --- 12. Multiple assigns to different vars in same block ---
TEST(ParserSection10, Sec10_6_1_MultipleAssignsDifferentVars) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c;\n"
      "  initial begin\n"
      "    assign a = 1;\n"
      "    assign b = 0;\n"
      "    assign c = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  auto* s2 = NthInitialStmt(r, 2);
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
  auto r = Parse(
      "module m;\n"
      "  reg q;\n"
      "  initial begin\n"
      "    deassign q;\n"
      "    q = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kDeassign);
  EXPECT_EQ(s1->kind, StmtKind::kBlockingAssign);
}

// --- 14. Assign with ternary expression RHS ---
TEST(ParserSection10, Sec10_6_1_AssignTernaryRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg q, sel, a, b;\n"
      "  initial begin\n"
      "    assign q = sel ? a : b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
}

// --- 15. Assign with function call RHS ---
TEST(ParserSection10, Sec10_6_1_AssignFunctionCallRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] q;\n"
      "  initial begin\n"
      "    assign q = compute(a, b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

// --- 16. Assign with unary operator RHS ---
TEST(ParserSection10, Sec10_6_1_AssignUnaryRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg a, q;\n"
      "  initial begin\n"
      "    assign q = ~a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kUnary);
}

// --- 17. Assign inside for loop ---
TEST(ParserSection10, Sec10_6_1_AssignInsideForLoop) {
  auto r = Parse(
      "module m;\n"
      "  reg [3:0] q;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 4; i++)\n"
      "      assign q[i] = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
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
  auto r = Parse(
      "module m;\n"
      "  reg q;\n"
      "  initial begin : my_block\n"
      "    assign q = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
}

// --- 20. Assign in fork-join ---
TEST(ParserSection10, Sec10_6_1_AssignInForkJoin) {
  auto r = Parse(
      "module m;\n"
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kAssign);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kAssign);
}

// §10.6.1: procedural deassign
TEST(ParserA604, StmtItemProceduralDeassign) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    deassign x;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDeassign);
}

TEST(ParserSection10, DeassignConcatLhs) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    deassign {a, b};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDeassign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
}

}  // namespace
