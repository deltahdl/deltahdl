#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ClockingScopeParse, InProgram) {
  EXPECT_TRUE(
      ParseOk("program test_prog(input clk, input [7:0] data);\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endprogram\n"));
}

TEST(ClockingScopeParse, ProgramWithClockingAndInitial) {
  EXPECT_TRUE(
      ParseOk("program p(input logic clk);\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "    output valid;\n"
              "  endclocking\n"
              "  initial begin\n"
              "    @(cb);\n"
              "    $display(\"synced\");\n"
              "  end\n"
              "endprogram\n"));
}

TEST(ClockingScopeParse, AmongOtherModuleItems) {
  auto r = Parse(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] data;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "cb");
  ASSERT_GE(r.cu->modules[0]->items.size(), 4u);
}

TEST(ClockingScopeParse, InChecker) {
  EXPECT_TRUE(
      ParseOk("checker my_check(input clk, input data);\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endchecker\n"));
}

TEST(ClockingScopeParse, DotAccessToClockvar) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking dom @(posedge clk);\n"
              "    input sig;\n"
              "  endclocking\n"
              "  initial begin\n"
              "    $display(dom.sig);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ClockingScopeParse, MultipleBlocksInModule) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb1 @(posedge clk);\n"
      "    input a;\n"
      "  endclocking\n"
      "  clocking cb2 @(negedge clk);\n"
      "    output b;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kClockingBlock) ++count;
  }
  EXPECT_EQ(count, 2);
}

}  // namespace
