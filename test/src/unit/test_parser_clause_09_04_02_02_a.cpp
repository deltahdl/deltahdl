#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ProceduralBlockSyntaxParsing, AlwaysConstruct_ImplicitSensitivityStar) {
  auto r = Parse(
      "module m;\n"
      "  always @* y = a + b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
}

TEST(ProceduralBlockSyntaxParsing, AlwaysConstruct_ImplicitSensitivityParenStar) {
  auto r = Parse(
      "module m;\n"
      "  always @(*) y = a + b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
}

TEST(ProcessParsing, AtStarAlwaysSimple) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  always @* a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
}

TEST(ProcessParsing, AtStarParenAlwaysSimple) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  always @(*) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
}

TEST(ProcessParsing, AtStarStmtLevelInitial) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    @* a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

TEST(ProcessParsing, AlwaysStarVarDecls) {
  auto r = Parse(
      "module m;\n"
      "  always @* begin\n"
      "    int temp;\n"
      "    temp = a + b;\n"
      "    y = temp;\n"
      "  end\n"
      "endmodule\n");
  VerifyAlwaysVarDecl(r);
}

TEST(ProcessParsing, AtStarParenStmtLevel) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    @(*) a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

TEST(ProcessParsing, AtStarBeginEndBlock) {
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
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

TEST(ProcessParsing, AtStarParenBeginEndBlock) {
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
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

TEST(ProcessParsing, AlwaysStarFunctionCall) {
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

TEST(ProcessParsing, AtStarIfElseBody) {
  auto r = Parse(
      "module m;\n"
      "  reg sel, a, b, out;\n"
      "  always @* if (sel) out = a; else out = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kIf);
  EXPECT_NE(item->body->condition, nullptr);
  EXPECT_NE(item->body->then_branch, nullptr);
  EXPECT_NE(item->body->else_branch, nullptr);
}

TEST(ProcessParsing, AtStarCaseBody) {
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
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
  EXPECT_EQ(item->body->case_items.size(), 3u);
}

TEST(ProcessParsing, AlwaysStarMultipleAssigns) {
  auto r = Parse(
      "module m;\n"
      "  always @* begin\n"
      "    x = a & b;\n"
      "    y = a | c;\n"
      "    z = a ^ d;\n"
      "  end\n"
      "endmodule\n");
  VerifyAlwaysMultiAssigns(r);
}

TEST(ProcessParsing, AtStarParenMultipleAssignments) {
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
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 3u);
}

static void VerifyStarEventControl(ParseResult& r) {
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

TEST(ProcessParsing, StmtLevelStarEventIsStarTrue) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @* a = b;\n"
      "  end\n"
      "endmodule\n");
  VerifyStarEventControl(r);
}

TEST(ProcessParsing, StmtLevelStarParenEventIsStarTrue) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(*) a = b;\n"
      "  end\n"
      "endmodule\n");
  VerifyStarEventControl(r);
}

TEST(ProcessParsing, AtStarInInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial @* a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  auto* stmt = item->body;
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

TEST(ProcessParsing, AtStarParenInInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial @(*) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

TEST(ProcessParsing, AlwaysStarNestedIfElseInBlock) {
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
  VerifyAlwaysNestedIfElse(r);
}

TEST(ProcessParsing, AtStarAlwaysSensitivityEmpty) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  always @* a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->sensitivity.size(), 0u);
  ASSERT_NE(item->body, nullptr);
}

TEST(ProcessParsing, AtStarParenAlwaysSensitivityEmpty) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  always @(*) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->sensitivity.size(), 0u);
  ASSERT_NE(item->body, nullptr);
}

TEST(ProcessParsing, AtStarNestedBlocks) {
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
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_EQ(item->body->stmts.size(), 2u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts[1]->kind, StmtKind::kBlock);
}

TEST(ProcessParsing, AtStarVarDeclInBody) {
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
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 2u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kVarDecl);
}

TEST(ProcessParsing, AtStarParenComplexCombLogic) {
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
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

TEST(ProcessParsing, AtStarFunctionCalls) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] a, result;\n"
      "  always @* begin\n"
      "    result = $clog2(a);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
}

TEST(ProcessParsing, AtStarForLoop) {
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
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kFor);
}
static ModuleItem* NthAlwaysItem(ParseResult& r, size_t n) {
  size_t count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) {
      if (count == n) return item;
      ++count;
    }
  }
  return nullptr;
}

TEST(ProcessParsing, MultipleAtStarBlocks) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c, x, y;\n"
      "  always @* x = a & b;\n"
      "  always @* y = b | c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item0 = NthAlwaysItem(r, 0);
  auto* item1 = NthAlwaysItem(r, 1);
  ASSERT_NE(item0, nullptr);
  ASSERT_NE(item1, nullptr);
  EXPECT_TRUE(item0->sensitivity.empty());
  EXPECT_TRUE(item1->sensitivity.empty());
  ASSERT_NE(item0->body, nullptr);
  ASSERT_NE(item1->body, nullptr);
}

TEST(ProcessParsing, AtStarCaseInside) {
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
  auto* case_stmt = GetAlwaysStarCaseStmt(r);
  ASSERT_NE(case_stmt, nullptr);
  EXPECT_EQ(case_stmt->case_items.size(), 4u);
}

TEST(ProcessParsing, AtStarPriorityCase) {
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
  auto* case_stmt = GetAlwaysStarCaseStmt(r);
  ASSERT_NE(case_stmt, nullptr);
  EXPECT_EQ(case_stmt->qualifier, CaseQualifier::kPriority);
}

TEST(ProcessParsing, AtStarConcatenation) {
  auto r = Parse(
      "module m;\n"
      "  reg [3:0] a, b;\n"
      "  reg [7:0] out;\n"
      "  always @* out = {a, b};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kConcatenation);
}

TEST(ProcessParsing, AtStarTernary) {
  auto r = Parse(
      "module m;\n"
      "  reg sel, a, b, out;\n"
      "  always @* out = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->body->rhs, nullptr);
  EXPECT_EQ(item->body->rhs->kind, ExprKind::kTernary);
}

TEST(ProcessParsing, IsStarEventTrueAtStarParen) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    @(*) a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_EQ(stmt->events.size(), 0u);
}

TEST(ProcessParsing, AtStarStmtBodyPresent) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    @* a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlockingAssign);
}

TEST(ProcessParsing, AtStarStmtLevelBeginEnd) {
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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->body->stmts.size(), 2u);
}

TEST(SchedulingSemanticsParsing, StarEventControl) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    @* a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

TEST(ProcessParsing, MultipleAtStarInInitial) {
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
  auto* s0 = NthInitialStmt(r, 0);
  auto* s1 = NthInitialStmt(r, 1);
  ASSERT_NE(s0, nullptr);
  ASSERT_NE(s1, nullptr);
  EXPECT_EQ(s0->kind, StmtKind::kEventControl);
  EXPECT_TRUE(s0->is_star_event);
  EXPECT_EQ(s1->kind, StmtKind::kEventControl);
  EXPECT_TRUE(s1->is_star_event);
}

TEST(ProcessParsing, ParseOkAtStarCombiModule) {
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

TEST(SchedulingSemanticsParsing, ParenStarEventControl) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    @(*) a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

TEST(ProcessParsing, ParseOkAtStarParenCombiModule) {
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

TEST(AssignmentParsing, FullPatternAlwaysComb) {
  EXPECT_TRUE(
      ParseOk("module m(\n"
              "  input [7:0] a, b,\n"
              "  input sel,\n"
              "  output reg [7:0] result\n"
              ");\n"
              "  always @(*) begin\n"
              "    result = 0;\n"
              "    if (sel)\n"
              "      result = a + b;\n"
              "    else\n"
              "      result = a - b;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ProcessParsing, AlwaysStarEmptySensitivity) {
  auto r = Parse(
      "module m;\n"
      "  always @* y = a | b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
}

TEST(ProcessParsing, AlwaysStarParenEquivalent) {
  auto r = Parse(
      "module m;\n"
      "  always @(*) y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  EXPECT_TRUE(item->sensitivity.empty());
}

}  // namespace
