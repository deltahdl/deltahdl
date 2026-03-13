#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(GlobalClockingElab, BasicGlobalClockingElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  global clocking gclk @(posedge sys_clk);\n"
             "  endclocking\n"
             "endmodule\n"));
}

TEST(GlobalClockingElab, UnnamedGlobalClockingElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  global clocking @(posedge clk); endclocking\n"
             "endmodule\n"));
}

TEST(GlobalClockingElab, CompoundEventElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  global clocking sys @(clk1 or clk2); endclocking\n"
             "endmodule\n"));
}

TEST(GlobalClockingElab, DuplicateGlobalClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  global clocking gc1 @(posedge clk1); endclocking\n"
      "  global clocking gc2 @(posedge clk2); endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(GlobalClockingElab, GlobalClockingInInterfaceElaborates) {
  EXPECT_TRUE(
      ElabOk("interface my_if (input clk);\n"
             "  global clocking gc @(posedge clk); endclocking\n"
             "endinterface\n"));
}

TEST(GlobalClockingElab, GlobalAndDefaultCoexist) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  global clocking gc @(posedge clk); endclocking\n"
             "  default clocking dc @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "endmodule\n"));
}

}  // namespace
