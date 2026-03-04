#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection12, ForeverWithTimingControl) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    forever begin\n"
              "      @(posedge clk);\n"
              "      x = ~x;\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA608, ForeverLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin forever #5 clk = ~clk; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ParserA608, ForeverNullStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin forever ; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
}

TEST(ParserSection12, ForeverLoopWithBlock) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    forever begin\n"
      "      @(posedge clk);\n"
      "      x = x + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

}
