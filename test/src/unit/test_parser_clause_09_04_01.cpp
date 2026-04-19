#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DelayParsing, DelayValueInStatement) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial #10 $display(\"hello\");\n"
              "endmodule"));
}

TEST(DelayControlParsing, ChainedDelayControls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #5 a = 0;\n"
      "    #10 a = 1;\n"
      "    #15 a = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(body->stmts[i]->kind, StmtKind::kDelay);
  }
}

TEST(DelayControlParsing, DelayWithExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #(a + b) c = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
}

TEST(DelayControlParsing, ZeroDelayControl) {
  auto r = Parse(
      "module m;\n"
      "  reg a;\n"
      "  initial begin\n"
      "    #0 a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(DelayControlParsing, UnitDelayControl) {
  auto r = Parse(
      "module m;\n"
      "  reg a;\n"
      "  initial begin\n"
      "    #1 a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(DelayControlParsing, DelayControlReal) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #3.5 a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
}

static ModuleItem* FindItemByKindFromResult(ParseResult& r,
                                            ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

static ModuleItem* FindInitialBlock(ParseResult& r) {
  return FindItemByKindFromResult(r, ModuleItemKind::kInitialBlock);
}

TEST(DelayControlParsing, InitialBlockWithDelays) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    #5 a = 1;\n"
      "    #10 b = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* init_item = FindInitialBlock(r);
  ASSERT_NE(init_item, nullptr);
  ASSERT_NE(init_item->body, nullptr);
  EXPECT_EQ(init_item->body->kind, StmtKind::kBlock);
  ASSERT_GE(init_item->body->stmts.size(), 2u);
  EXPECT_EQ(init_item->body->stmts[0]->kind, StmtKind::kDelay);
  EXPECT_EQ(init_item->body->stmts[1]->kind, StmtKind::kDelay);
}


TEST(DelayControlParsing, DelayControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #10 a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(DelayControlParsing, DelayWithNullStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #10;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
}

TEST(DelayControlParsing, IdentifierAsDelayValue) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #tDelay a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_EQ(stmt->delay->kind, ExprKind::kIdentifier);
}

}  // namespace
