#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ImplicitEventParsing, AtStarAlwaysSimple) {
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

TEST(ImplicitEventParsing, AtStarParenAlwaysSimple) {
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

TEST(ImplicitEventParsing, AtStarStmtLevelInitial) {
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

TEST(ImplicitEventParsing, AtStarParenStmtLevel) {
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

TEST(ImplicitEventParsing, AtStarBeginEndBlock) {
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

TEST(ImplicitEventParsing, AtStarIfElseBody) {
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

TEST(ImplicitEventParsing, AtStarCaseBody) {
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

TEST(ImplicitEventParsing, AtStarNestedBlocks) {
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

TEST(ImplicitEventParsing, AtStarVarDeclInBody) {
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

TEST(ImplicitEventParsing, AtStarFunctionCalls) {
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

TEST(ImplicitEventParsing, AtStarForLoop) {
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

TEST(ImplicitEventParsing, MultipleAtStarBlocks) {
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

TEST(ImplicitEventParsing, AtStarPriorityCase) {
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

TEST(ImplicitEventParsing, AtStarConcatenation) {
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

TEST(ImplicitEventParsing, AtStarTernary) {
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

TEST(ImplicitEventParsing, NestedAtStarParsesAsEventControl) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c, d, x;\n"
      "  always @* begin\n"
      "    x = a ^ b;\n"
      "    @* x = c ^ d;\n"
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
  auto* nested = item->body->stmts[1];
  EXPECT_EQ(nested->kind, StmtKind::kEventControl);
  EXPECT_TRUE(nested->is_star_event);
  EXPECT_TRUE(nested->events.empty());
  ASSERT_NE(nested->body, nullptr);
  EXPECT_EQ(nested->body->kind, StmtKind::kBlockingAssign);
}

TEST(ImplicitEventParsing, AtStarWithLhsIndexSelect) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] y;\n"
      "  reg [2:0] a;\n"
      "  reg en;\n"
      "  always @* begin\n"
      "    y = 8'hff;\n"
      "    y[a] = !en;\n"
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
  auto* assign = item->body->stmts[1];
  EXPECT_EQ(assign->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(assign->lhs, nullptr);
  EXPECT_EQ(assign->lhs->kind, ExprKind::kSelect);
}

}
