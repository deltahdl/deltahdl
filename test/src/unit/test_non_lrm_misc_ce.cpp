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


// --- 9. Nonblocking to concatenation LHS: {q1, q2} <= {d1, d2} ---
TEST(ParserSection10, Sec10_4_2_ConcatenationLhsRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg q1, q2, d1, d2;\n"
      "  initial begin\n"
      "    {q1, q2} <= {d1, d2};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->lhs->elements.size(), 2u);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements.size(), 2u);
}

// --- 10. Nonblocking with ternary RHS: q <= sel ? a : b ---
TEST(ParserSection10, Sec10_4_2_TernaryRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg q, sel, a, b;\n"
      "  initial begin\n"
      "    q <= sel ? a : b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
}

// --- 11. Nonblocking in begin-end block ---
TEST(ParserSection10, Sec10_4_2_InBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  reg q, d;\n"
      "  initial begin\n"
      "    q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_EQ(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kNonblockingAssign);
}

// --- 12. Nonblocking in if-else branches (mux pattern) ---
TEST(ParserSection10, Sec10_4_2_IfElseMuxPattern) {
  auto r = Parse(
      "module m;\n"
      "  reg q, sel, a, b;\n"
      "  initial begin\n"
      "    if (sel)\n"
      "      q <= a;\n"
      "    else\n"
      "      q <= b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kNonblockingAssign);
}

// --- 13. Nonblocking in case statement (decoder pattern) ---
TEST(ParserSection10, Sec10_4_2_CaseDecoderPattern) {
  auto r = Parse(
      "module m;\n"
      "  reg [1:0] sel;\n"
      "  reg [7:0] q;\n"
      "  initial begin\n"
      "    case (sel)\n"
      "      2'b00: q <= 8'h00;\n"
      "      2'b01: q <= 8'h01;\n"
      "      2'b10: q <= 8'h10;\n"
      "      default: q <= 8'hFF;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_GE(stmt->case_items.size(), 4u);
  EXPECT_EQ(stmt->case_items[0].body->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(stmt->case_items[1].body->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(stmt->case_items[2].body->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(stmt->case_items[3].body->kind, StmtKind::kNonblockingAssign);
}

// --- 14. Multiple nonblocking assignments in same block ---
TEST(ParserSection10, Sec10_4_2_MultipleInSameBlock) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c, d;\n"
      "  initial begin\n"
      "    a <= b;\n"
      "    c <= d;\n"
      "    b <= a;\n"
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
  EXPECT_EQ(s0->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(s1->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(s2->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(s0->lhs->text, "a");
  EXPECT_EQ(s1->lhs->text, "c");
  EXPECT_EQ(s2->lhs->text, "b");
}

// --- 15. Nonblocking with function call RHS ---
TEST(ParserSection10, Sec10_4_2_FunctionCallRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] q;\n"
      "  initial begin\n"
      "    q <= compute(a, b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

// --- 16. Nonblocking with system call RHS ---
TEST(ParserSection10, Sec10_4_2_SystemCallRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [31:0] q;\n"
      "  initial begin\n"
      "    q <= $random;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSystemCall);
}

// --- 17. Nonblocking to struct member: s.field <= val ---
TEST(ParserSection10, Sec10_4_2_StructMemberLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    s.field <= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
  ASSERT_NE(stmt->rhs, nullptr);
}

// --- 18. Nonblocking to array element: mem[idx] <= data ---
TEST(ParserSection10, Sec10_4_2_ArrayElementLhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] mem [0:255];\n"
      "  initial begin\n"
      "    mem[0] <= 8'hAB;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->rhs, nullptr);
}

// --- 19. Nonblocking with replication RHS ---
TEST(ParserSection10, Sec10_4_2_ReplicationRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] q;\n"
      "  initial begin\n"
      "    q <= {4{2'b10}};\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kReplicate);
}

// --- 20. Nonblocking with cast RHS ---
TEST(ParserSection10, Sec10_4_2_CastRhs) {
  auto r = Parse(
      "module m;\n"
      "  int q;\n"
      "  initial begin\n"
      "    q <= int'(3.14);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCast);
}

// --- 21. Nonblocking with repeat event control ---
TEST(ParserSection10, Sec10_4_2_RepeatEventControl) {
  auto r = Parse(
      "module m;\n"
      "  reg q, d, clk;\n"
      "  initial begin\n"
      "    q <= repeat(3) @(posedge clk) d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->text, "d");
}

// --- 22. Nonblocking mixed with blocking in same module (different blocks) ---
TEST(ParserSection10, Sec10_4_2_MixedBlockingNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  reg q, d, a, b;\n"
      "  always @(posedge clk)\n"
      "    q <= d;\n"
      "  always @(*)\n"
      "    a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  int always_count = 0;
  bool found_nonblocking = false;
  bool found_blocking = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) {
      always_count++;
      if (item->body && item->body->kind == StmtKind::kNonblockingAssign) {
        found_nonblocking = true;
      }
      if (item->body && item->body->kind == StmtKind::kBlockingAssign) {
        found_blocking = true;
      }
    }
  }
  EXPECT_EQ(always_count, 2);
  EXPECT_TRUE(found_nonblocking);
  EXPECT_TRUE(found_blocking);
}

// --- 23. Nonblocking in always_ff with reset pattern ---
TEST(ParserSection10, Sec10_4_2_AlwaysFFResetPattern) {
  auto r = Parse(
      "module m;\n"
      "  always_ff @(posedge clk or negedge rst_n) begin\n"
      "    if (!rst_n)\n"
      "      q <= 0;\n"
      "    else\n"
      "      q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysFFBlock);
  ASSERT_GE(item->sensitivity.size(), 2u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_EQ(item->sensitivity[1].edge, Edge::kNegedge);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  auto* if_stmt = item->body->stmts[0];
  EXPECT_EQ(if_stmt->kind, StmtKind::kIf);
  ASSERT_NE(if_stmt->then_branch, nullptr);
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(if_stmt->else_branch, nullptr);
  EXPECT_EQ(if_stmt->else_branch->kind, StmtKind::kNonblockingAssign);
}

// --- 24. Nonblocking with negedge intra-assignment event ---
TEST(ParserSection10, Sec10_4_2_IntraAssignEventNegedge) {
  auto r = Parse(
      "module m;\n"
      "  reg q, d, clk;\n"
      "  initial begin\n"
      "    q <= @(negedge clk) d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
  ASSERT_NE(stmt->rhs, nullptr);
}

// --- 25. Nonblocking with complex expression (shift and mask) ---
TEST(ParserSection10, Sec10_4_2_ComplexExpressionRhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] q, data;\n"
      "  initial begin\n"
      "    q <= (data << 2) | 8'h03;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
}

// --- 26. Nonblocking to indexed part-select (q[base +: width]) ---
TEST(ParserSection10, Sec10_4_2_IndexedPartSelectLhs) {
  auto r = Parse(
      "module m;\n"
      "  reg [31:0] q;\n"
      "  initial begin\n"
      "    q[8 +: 8] <= 8'hAB;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->rhs, nullptr);
}

// --- 27. Nonblocking in named begin-end block ---
TEST(ParserSection10, Sec10_4_2_NamedBlockNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  reg q, d;\n"
      "  initial begin : my_block\n"
      "    q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "my_block");
  ASSERT_EQ(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kNonblockingAssign);
}

// --- 28. Pipeline pattern with multiple nonblocking assignments ---
TEST(ParserSection10, Sec10_4_2_PipelinePattern) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  reg [7:0] stage1, stage2, stage3, d;\n"
              "  always_ff @(posedge clk) begin\n"
              "    stage1 <= d;\n"
              "    stage2 <= stage1;\n"
              "    stage3 <= stage2;\n"
              "  end\n"
              "endmodule\n"));
}

// --- 29. Nonblocking swap pattern ---
TEST(ParserSection10, Sec10_4_2_SwapPattern) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] a, b;\n"
      "  initial begin\n"
      "    a <= b;\n"
      "    b <= a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(s1->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(s0->lhs->text, "a");
  EXPECT_EQ(s0->rhs->text, "b");
  EXPECT_EQ(s1->lhs->text, "b");
  EXPECT_EQ(s1->rhs->text, "a");
}

// --- 30. Full register file pattern with nonblocking in always_ff ---
TEST(ParserSection10, Sec10_4_2_RegisterFilePattern) {
  auto r = Parse(
      "module m;\n"
      "  always_ff @(posedge clk) begin\n"
      "    if (wr_en)\n"
      "      regfile[wr_addr] <= wr_data;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysFFBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  auto* if_stmt = item->body->stmts[0];
  EXPECT_EQ(if_stmt->kind, StmtKind::kIf);
  ASSERT_NE(if_stmt->then_branch, nullptr);
  EXPECT_EQ(if_stmt->then_branch->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(if_stmt->then_branch->lhs, nullptr);
  EXPECT_EQ(if_stmt->then_branch->lhs->kind, ExprKind::kSelect);
}

TEST(Parser, ExpressionPrecedence) {
  auto r = Parse(
      "module expr;\n"
      "  logic a;\n"
      "  assign a = 1 + 2 * 3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

struct LetParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static LetParseResult Parse(const std::string& src) {
  LetParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// Helper: find the first kLetDecl item in the first module.
static ModuleItem* FirstLetDecl(LetParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kLetDecl) return item;
  }
  return nullptr;
}

// ==========================================================================
// §11.12: Let declaration parsing
// ==========================================================================
TEST(ParserLet, DeclNoArgsParse) {
  auto r = Parse(
      "module t;\n"
      "  let addr = top.block1.base + top.block1.displ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  EXPECT_EQ(let_item->name, "addr");
}

TEST(ParserLet, DeclNoArgsBody) {
  auto r = Parse(
      "module t;\n"
      "  let addr = top.block1.base + top.block1.displ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  EXPECT_TRUE(let_item->func_args.empty());
  ASSERT_NE(let_item->init_expr, nullptr);
}

TEST(ParserLet, DeclWithArgsParse) {
  auto r = Parse(
      "module t;\n"
      "  let op(x, y, z) = |((x | y) & z);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  EXPECT_EQ(let_item->name, "op");
}

TEST(ParserLet, DeclWithArgsNames) {
  auto r = Parse(
      "module t;\n"
      "  let op(x, y, z) = |((x | y) & z);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  ASSERT_EQ(let_item->func_args.size(), 3u);
  const char* const kExpected[] = {"x", "y", "z"};
  for (size_t i = 0; i < 3; i++) {
    EXPECT_EQ(let_item->func_args[i].name, kExpected[i]);
  }
  ASSERT_NE(let_item->init_expr, nullptr);
}

TEST(ParserLet, DeclWithDefaultsParse) {
  auto r = Parse(
      "module t;\n"
      "  let at_least_two(sig, rst = 1'b0) = rst || sig;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  EXPECT_EQ(let_item->name, "at_least_two");
  ASSERT_EQ(let_item->func_args.size(), 2u);
}

TEST(ParserLet, DeclWithDefaultsArgs) {
  auto r = Parse(
      "module t;\n"
      "  let at_least_two(sig, rst = 1'b0) = rst || sig;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  EXPECT_EQ(let_item->func_args[0].name, "sig");
  EXPECT_EQ(let_item->func_args[0].default_value, nullptr);
  EXPECT_EQ(let_item->func_args[1].name, "rst");
  EXPECT_NE(let_item->func_args[1].default_value, nullptr);
}

TEST(ParserLet, DeclTypedArgsParse) {
  auto r = Parse(
      "module t;\n"
      "  let mult(logic [15:0] x, logic [15:0] y) = x * y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  EXPECT_EQ(let_item->name, "mult");
}

TEST(ParserLet, DeclTypedArgsNames) {
  auto r = Parse(
      "module t;\n"
      "  let mult(logic [15:0] x, logic [15:0] y) = x * y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  ASSERT_EQ(let_item->func_args.size(), 2u);
  EXPECT_EQ(let_item->func_args[0].name, "x");
  EXPECT_EQ(let_item->func_args[1].name, "y");
}

TEST(ParserLet, DeclUntypedArg) {
  auto r = Parse(
      "module t;\n"
      "  let check(untyped a) = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  ASSERT_EQ(let_item->func_args.size(), 1u);
  EXPECT_EQ(let_item->func_args[0].name, "a");
}

TEST(ParserLet, DeclEmptyParens) {
  auto r = Parse(
      "module t;\n"
      "  let empty_let() = 42;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* let_item = FirstLetDecl(r);
  ASSERT_NE(let_item, nullptr);
  EXPECT_EQ(let_item->name, "empty_let");
  EXPECT_TRUE(let_item->func_args.empty());
}

// ==========================================================================
// §11.12: Let instantiation parsing (calls parsed as kCall expressions)
// ==========================================================================
TEST(ParserLet, InstantiationParsed) {
  // Let calls look syntactically like function calls — verify parsing.
  auto r = Parse(
      "module t;\n"
      "  let op(x, y) = x + y;\n"
      "  initial begin\n"
      "    int z;\n"
      "    z = op(3, 4);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserLet, InstantiationNamedArgs) {
  auto r = Parse(
      "module t;\n"
      "  let valid_arb(request, valid, override) = "
      "|(request & valid) || override;\n"
      "  initial begin\n"
      "    logic result;\n"
      "    result = valid_arb(.request(2'b11), .valid(2'b10),"
      " .override(1'b0));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserLet, InstantiationDefaultArgs) {
  auto r = Parse(
      "module t;\n"
      "  let at_least_two(sig, rst = 1'b0) = rst || sig;\n"
      "  initial begin\n"
      "    logic [15:0] sig1;\n"
      "    logic q;\n"
      "    q = at_least_two(sig1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ==========================================================================
// §11.12: Let in package scope
// ==========================================================================
TEST(ParserLet, DeclInPackage) {
  auto r = Parse(
      "package pkg;\n"
      "  let my_op(x, y) = x & y;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.2.8 block_item_declaration alternative 4: let_declaration
TEST(ParserA28, LetDeclInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    let my_add(x, y) = x + y;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA28, LetDeclNoArgsInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    let val = 42;\n"
              "  end\n"
              "endmodule\n"));
}

// let_declaration in task body
TEST(ParserA28, LetDeclInTask) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task my_task();\n"
              "    let inc(x) = x + 1;\n"
              "  endtask\n"
              "endmodule\n"));
}

// let_declaration in fork/join
TEST(ParserA28, LetDeclInForkJoin) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial fork\n"
              "    let val = 99;\n"
              "  join\n"
              "endmodule\n"));
}

TEST(ParserA210, AssertionItemDecl_LetDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  let max(a, b) = (a > b) ? a : b;\n"
              "endmodule\n"));
}

struct ParseResult11 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult11 Parse(const std::string& src) {
  ParseResult11 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult11& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

// Helper: get the RHS of the first blocking assignment in initial block.
static Expr* FirstAssignRhs(ParseResult11& r) {
  auto* stmt = FirstInitialStmt(r);
  if (!stmt) return nullptr;
  return stmt->rhs;
}

// =========================================================================
// Section 11.3.6 -- Assignment operators in expressions
// =========================================================================
TEST(ParserSection11, CompoundAssignPlusEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a += 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  // Compound assignment is parsed as blocking assign with op
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection11, CompoundAssignMinusEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a -= 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection11, CompoundAssignStarEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a *= 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignSlashEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a /= 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignPercentEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a %= 3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignAmpEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a &= 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignPipeEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a |= 8'h0F;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignCaretEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a ^= b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignLtLtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a <<= 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignGtGtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a >>= 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignLtLtLtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a <<<= 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, CompoundAssignGtGtGtEq) {
  auto r = Parse(
      "module t;\n"
      "  initial a >>>= 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection11, PostfixIncrementParses) {
  auto r = Parse(
      "module t;\n"
      "  initial a++;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(ParserSection11, PostfixIncrementOp) {
  auto r = Parse(
      "module t;\n"
      "  initial a++;\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(stmt->expr->op, TokenKind::kPlusPlus);
}

TEST(ParserSection11, PostfixDecrementParses) {
  auto r = Parse(
      "module t;\n"
      "  initial a--;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(ParserSection11, PostfixDecrementOp) {
  auto r = Parse(
      "module t;\n"
      "  initial a--;\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(stmt->expr->op, TokenKind::kMinusMinus);
}

// =========================================================================
// Section 11.4.13 -- Inside operator (set membership)
// =========================================================================
TEST(ParserSection11, InsideBasicListParses) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a inside {1, 2, 3}) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
}

}  // namespace
