#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(GlobalClockingParse, GlobalKeywordSetsFlag) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  global clocking gclk @(posedge clk); endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_FALSE(item->is_default_clocking);
  EXPECT_EQ(item->name, "gclk");
  EXPECT_FALSE(r.has_errors);
}

TEST(GlobalClockingParse, AnonymousGlobalClocking) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  global clocking @(posedge clk); endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_TRUE(item->name.empty());
  EXPECT_FALSE(r.has_errors);
}

TEST(GlobalClockingParse, GlobalClockingInGenerateBlockIsError) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  if (1) begin : g\n"
      "    global clocking gclk @(posedge clk); endclocking\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(GlobalClockingParse, RegularClockingInGenerateBlockIsAllowed) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic clk;\n"
              "  if (1) begin : g\n"
              "    clocking cb @(posedge clk); endclocking\n"
              "  end\n"
              "endmodule\n"));
}

TEST(GlobalClockingParse, GlobalClockingInInterfaceParses) {
  EXPECT_TRUE(
      ParseOk("interface ifc;\n"
              "  logic clk;\n"
              "  global clocking gclk @(posedge clk); endclocking\n"
              "endinterface\n"));
}

TEST(GlobalClockingParse, GlobalClockingInProgramParses) {
  EXPECT_TRUE(
      ParseOk("program p;\n"
              "  logic clk;\n"
              "  global clocking gclk @(posedge clk); endclocking\n"
              "endprogram\n"));
}

TEST(GlobalClockingParse, GlobalClockingInCheckerParses) {
  EXPECT_TRUE(
      ParseOk("checker chk;\n"
              "  logic clk;\n"
              "  global clocking gclk @(posedge clk); endclocking\n"
              "endchecker\n"));
}

TEST(GlobalClockingParse, MatchingEndLabelAccepted) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  global clocking gclk @(posedge clk); endclocking : gclk\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_EQ(item->name, "gclk");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
