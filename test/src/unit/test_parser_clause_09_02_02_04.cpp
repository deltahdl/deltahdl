#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(AlwaysFFParsing, BlockInAlwaysFFWithSensitivity) {
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
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kIf);
}
TEST(AlwaysFFParsing, AlwaysFFBlock) {
  auto r = Parse(
      "module counter(input logic clk, rst);\n"
      "  logic [7:0] count;\n"
      "  always_ff @(posedge clk or posedge rst)\n"
      "    if (rst) count <= '0;\n"
      "    else count <= count + 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  bool found_ff = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kAlwaysFFBlock &&
        item->always_kind == AlwaysKind::kAlwaysFF) {
      found_ff = true;
    }
  }
  EXPECT_TRUE(found_ff);
}

TEST(AlwaysFFParsing, AlwaysFFResetPattern) {
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

TEST(AlwaysFFParsing, AlwaysFFParsingWithIfElseChain) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, rst, d, q;\n"
      "  always_ff @(posedge clk or posedge rst) begin\n"
      "    if (rst) q <= 0;\n"
      "    else q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysFF);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kIf);
}

TEST(AlwaysFFParsing, VarDrivenByAlwaysFF) {
  auto r = Parse(
      "module t;\n"
      "  logic clk, q, d;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  bool found_ff = false;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kAlwaysFFBlock) {
      found_ff = true;
      ASSERT_NE(item->body, nullptr);
    }
  }
  EXPECT_TRUE(found_ff);
}
TEST(AlwaysFFParsing, AlwaysFFSimplePosedge) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  logic [3:0] count;\n"
      "  always_ff @(posedge clk)\n"
      "    count <= count + 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysFF);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
}

TEST(AlwaysFFParsing, AlwaysFF) {
  auto r = Parse(
      "module m;\n"
      "  reg q, d, clk;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysFFBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysFF);
  ASSERT_FALSE(item->sensitivity.empty());
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
}

TEST(AlwaysFFParsing, AlwaysFFWithNegedge) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always_ff @(negedge clk)\n"
              "    q <= d;\n"
              "endmodule\n"));
}
TEST(AlwaysFFParsing, AlwaysFF) {
  auto r = Parse(
      "module m;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysFF);
  ASSERT_FALSE(item->sensitivity.empty());
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
}

TEST(AlwaysFFParsing, AlwaysFFParsingFlipFlop) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  always_ff @(posedge clk) begin\n"
      "    q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysFFBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysFF);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
}

TEST(AlwaysFFParsing, PosedgeTriggered) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic clk, d, q;\n"
              "  always_ff @(posedge clk) q <= d;\n"
              "endmodule\n"));
}

}  // namespace
