#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(CycleDelayParse, IntegralNumber) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CycleDelayParse, Identifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ##n;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CycleDelayParse, ParenthesizedExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ##(j + 1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CycleDelayParse, ZeroCycleDelay) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ##0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CycleDelayParse, CycleDelayInClockingDrive) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    cb.data <= ##n 8'h42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CycleDelayParse, CycleDelayStmtKind) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  auto& items = r.cu->modules[0]->items;
  ASSERT_FALSE(items.empty());
  auto* body = items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_FALSE(body->stmts.empty());
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kCycleDelay);
  EXPECT_NE(body->stmts[0]->cycle_delay, nullptr);
}

TEST(CycleDelayParse, WithDefaultClocking) {
  EXPECT_TRUE(
      ParseOk("program test(input logic clk, input logic [15:0] data);\n"
              "  default clocking bus @(posedge clk);\n"
              "    inout data;\n"
              "  endclocking\n"
              "  initial begin\n"
              "    ##5;\n"
              "    if (bus.data == 10)\n"
              "      ##1;\n"
              "  end\n"
              "endprogram\n"));
}

}  // namespace
