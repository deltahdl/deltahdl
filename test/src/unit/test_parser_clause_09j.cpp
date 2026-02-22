#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult9j {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult9j Parse(const std::string &src) {
  ParseResult9j result;
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

static ModuleItem *FirstAlwaysItem(ParseResult9j &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) return item;
  }
  return nullptr;
}

static ModuleItem *NthAlwaysItem(ParseResult9j &r, size_t n) {
  size_t count = 0;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) {
      if (count == n) return item;
      ++count;
    }
  }
  return nullptr;
}

static Stmt *FirstInitialStmt(ParseResult9j &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static Stmt *NthInitialStmt(ParseResult9j &r, size_t n) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      if (n < item->body->stmts.size()) return item->body->stmts[n];
    }
  }
  return nullptr;
}

// =============================================================================
// LRM section 9.4.2.3 -- Implicit event_expression list (@* and @(*))
// =============================================================================

// @* at always block level: always @* stmt
TEST(ParserSection9, Sec9_4_2_3_AtStarAlwaysSimple) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  always @* a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
}

// @(*) at always block level: always @(*) stmt
TEST(ParserSection9, Sec9_4_2_3_AtStarParenAlwaysSimple) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  always @(*) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
}

// @* at statement level inside initial: produces kEventControl with
// is_star_event=true
TEST(ParserSection9, Sec9_4_2_3_AtStarStmtLevelInitial) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    @* a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

// @(*) at statement level: produces kEventControl with is_star_event=true
TEST(ParserSection9, Sec9_4_2_3_AtStarParenStmtLevel) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    @(*) a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

// @* with begin-end block body at always level
TEST(ParserSection9, Sec9_4_2_3_AtStarBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c;\n"
      "  always @* begin\n"
      "    a = b;\n"
      "    c = a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

// @(*) with begin-end block body at always level
TEST(ParserSection9, Sec9_4_2_3_AtStarParenBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c;\n"
      "  always @(*) begin\n"
      "    a = b;\n"
      "    c = a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

// @* with if-else body
TEST(ParserSection9, Sec9_4_2_3_AtStarIfElseBody) {
  auto r = Parse(
      "module m;\n"
      "  reg sel, a, b, out;\n"
      "  always @* if (sel) out = a; else out = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kIf);
  EXPECT_NE(item->body->condition, nullptr);
  EXPECT_NE(item->body->then_branch, nullptr);
  EXPECT_NE(item->body->else_branch, nullptr);
}

// @* with case body
TEST(ParserSection9, Sec9_4_2_3_AtStarCaseBody) {
  auto r = Parse(
      "module m;\n"
      "  reg [1:0] sel;\n"
      "  reg [7:0] out;\n"
      "  always @* case (sel)\n"
      "    2'b00: out = 8'h00;\n"
      "    2'b01: out = 8'h11;\n"
      "    default: out = 8'hFF;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_EQ(item->body->case_items.size(), 3u);
}

// @(*) with multiple assignments in begin-end
TEST(ParserSection9, Sec9_4_2_3_AtStarParenMultipleAssignments) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c, d, x, y, z;\n"
      "  always @(*) begin\n"
      "    x = a & b;\n"
      "    y = c | d;\n"
      "    z = x ^ y;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 3u);
}

// @* in initial block (statement-level event control)
TEST(ParserSection9, Sec9_4_2_3_AtStarInInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial @* a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  auto *stmt = item->body;
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

// @(*) in initial block
TEST(ParserSection9, Sec9_4_2_3_AtStarParenInInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial @(*) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

// @* in always block -- sensitivity list is empty, body is the statement
TEST(ParserSection9, Sec9_4_2_3_AtStarAlwaysSensitivityEmpty) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  always @* a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->sensitivity.size(), 0u);
  ASSERT_NE(item->body, nullptr);
}

// @(*) in always block -- same: sensitivity empty, body is statement
TEST(ParserSection9, Sec9_4_2_3_AtStarParenAlwaysSensitivityEmpty) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  always @(*) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->sensitivity.size(), 0u);
  ASSERT_NE(item->body, nullptr);
}

// @* with nested blocks
TEST(ParserSection9, Sec9_4_2_3_AtStarNestedBlocks) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c;\n"
      "  always @* begin\n"
      "    begin\n"
      "      a = b;\n"
      "    end\n"
      "    begin\n"
      "      c = a;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_EQ(item->body->stmts.size(), 2u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts[1]->kind, StmtKind::kBlock);
}

// @* with variable declarations in body
TEST(ParserSection9, Sec9_4_2_3_AtStarVarDeclInBody) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  always @* begin\n"
      "    int temp;\n"
      "    temp = a + b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 2u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kVarDecl);
}

// @(*) with complex combinational logic
TEST(ParserSection9, Sec9_4_2_3_AtStarParenComplexCombLogic) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] a, b, c, sum, product;\n"
      "  always @(*) begin\n"
      "    sum = a + b + c;\n"
      "    product = a * b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

// @* with function calls in body
TEST(ParserSection9, Sec9_4_2_3_AtStarFunctionCalls) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] a, result;\n"
      "  always @* begin\n"
      "    result = $clog2(a);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
}

// @* with for loop in body
TEST(ParserSection9, Sec9_4_2_3_AtStarForLoop) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] data [0:3];\n"
      "  reg [7:0] out [0:3];\n"
      "  always @* begin\n"
      "    for (int i = 0; i < 4; i++)\n"
      "      out[i] = data[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kFor);
}

// Multiple @* blocks in same module
TEST(ParserSection9, Sec9_4_2_3_MultipleAtStarBlocks) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c, x, y;\n"
      "  always @* x = a & b;\n"
      "  always @* y = b | c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item0 = NthAlwaysItem(r, 0);
  auto *item1 = NthAlwaysItem(r, 1);
  ASSERT_NE(item0, nullptr);
  ASSERT_NE(item1, nullptr);
  EXPECT_TRUE(item0->sensitivity.empty());
  EXPECT_TRUE(item1->sensitivity.empty());
  ASSERT_NE(item0->body, nullptr);
  ASSERT_NE(item1->body, nullptr);
}

// @* with case inside body
TEST(ParserSection9, Sec9_4_2_3_AtStarCaseInside) {
  auto r = Parse(
      "module m;\n"
      "  reg [1:0] sel;\n"
      "  reg [7:0] out, a, b, c, d;\n"
      "  always @* begin\n"
      "    case (sel)\n"
      "      2'd0: out = a;\n"
      "      2'd1: out = b;\n"
      "      2'd2: out = c;\n"
      "      default: out = d;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  ASSERT_GE(item->body->stmts.size(), 1u);
  auto *case_stmt = item->body->stmts[0];
  EXPECT_EQ(case_stmt->kind, StmtKind::kCase);
  EXPECT_EQ(case_stmt->case_items.size(), 4u);
}

// @* with unique case
TEST(ParserSection9, Sec9_4_2_3_AtStarUniqueCase) {
  auto r = Parse(
      "module m;\n"
      "  reg [1:0] sel;\n"
      "  reg out;\n"
      "  always @* begin\n"
      "    unique case (sel)\n"
      "      2'b00: out = 0;\n"
      "      2'b01: out = 1;\n"
      "      default: out = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  ASSERT_GE(item->body->stmts.size(), 1u);
  auto *case_stmt = item->body->stmts[0];
  EXPECT_EQ(case_stmt->kind, StmtKind::kCase);
  EXPECT_EQ(case_stmt->qualifier, CaseQualifier::kUnique);
}

// @* with priority case
TEST(ParserSection9, Sec9_4_2_3_AtStarPriorityCase) {
  auto r = Parse(
      "module m;\n"
      "  reg [1:0] sel;\n"
      "  reg out;\n"
      "  always @* begin\n"
      "    priority case (sel)\n"
      "      2'b00: out = 0;\n"
      "      default: out = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  ASSERT_GE(item->body->stmts.size(), 1u);
  auto *case_stmt = item->body->stmts[0];
  EXPECT_EQ(case_stmt->kind, StmtKind::kCase);
  EXPECT_EQ(case_stmt->qualifier, CaseQualifier::kPriority);
}

// @* with concatenation assignments
TEST(ParserSection9, Sec9_4_2_3_AtStarConcatenation) {
  auto r = Parse(
      "module m;\n"
      "  reg [3:0] a, b;\n"
      "  reg [7:0] out;\n"
      "  always @* out = {a, b};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kConcatenation);
}

// @* with ternary expression assignment
TEST(ParserSection9, Sec9_4_2_3_AtStarTernary) {
  auto r = Parse(
      "module m;\n"
      "  reg sel, a, b, out;\n"
      "  always @* out = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kTernary);
}

// Verify is_star_event is true and events empty for @(*) at statement level
TEST(ParserSection9, Sec9_4_2_3_IsStarEventTrueAtStarParen) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    @(*) a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_EQ(stmt->events.size(), 0u);
}

// @* body is present for statement-level event control
TEST(ParserSection9, Sec9_4_2_3_AtStarStmtBodyPresent) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    @* a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlockingAssign);
}

// @* statement level with begin-end block
TEST(ParserSection9, Sec9_4_2_3_AtStarStmtLevelBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c;\n"
      "  initial begin\n"
      "    @* begin\n"
      "      a = b;\n"
      "      c = a;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->body->stmts.size(), 2u);
}

// Multiple @* event controls in sequence inside initial block
TEST(ParserSection9, Sec9_4_2_3_MultipleAtStarInInitial) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c, d;\n"
      "  initial begin\n"
      "    @* a = b;\n"
      "    @(*) c = d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *s0 = NthInitialStmt(r, 0);
  auto *s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kEventControl);
  EXPECT_TRUE(s0->is_star_event);
  EXPECT_EQ(s1->kind, StmtKind::kEventControl);
  EXPECT_TRUE(s1->is_star_event);
}

// ParseOk: @* parses without errors in a typical combinational module
TEST(ParserSection9, Sec9_4_2_3_ParseOkAtStarCombiModule) {
  EXPECT_TRUE(
      ParseOk("module mux4(\n"
              "  input [1:0] sel,\n"
              "  input [7:0] a, b, c, d,\n"
              "  output reg [7:0] out\n"
              ");\n"
              "  always @* begin\n"
              "    case (sel)\n"
              "      2'd0: out = a;\n"
              "      2'd1: out = b;\n"
              "      2'd2: out = c;\n"
              "      default: out = d;\n"
              "    endcase\n"
              "  end\n"
              "endmodule\n"));
}

// ParseOk: @(*) parses without errors in a typical combinational module
TEST(ParserSection9, Sec9_4_2_3_ParseOkAtStarParenCombiModule) {
  EXPECT_TRUE(
      ParseOk("module adder(\n"
              "  input [7:0] a, b,\n"
              "  output reg [8:0] sum\n"
              ");\n"
              "  always @(*) begin\n"
              "    sum = a + b;\n"
              "  end\n"
              "endmodule\n"));
}
