#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection9, Sec9_2_2_WhileLoop) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] val;\n"
      "  logic [3:0] count;\n"
      "  always_comb begin\n"
      "    count = 0;\n"
      "    while (val[count] && count < 8)\n"
      "      count = count + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysComb(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 2u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(item->body->stmts[1]->kind, StmtKind::kWhile);
}

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

TEST(ParserSection12, WhileWithNullBody) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    while (0) ;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA608, WhileLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin while (x > 0) x = x - 1; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ParserA608, WhileNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin while (x > 0) ; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
}

TEST(ParserSection12, WhileLoopWithBlock) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    while (x > 0) begin\n"
      "      x = x - 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

}  // namespace
