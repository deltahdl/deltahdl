#include "fixture_elaborator.h"

namespace {

TEST(LexicalConventionElaboration, ModuleWithTimeLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial #10ns;\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, FixedPointTimeLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial #2.5us;\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, AllSixUnitsElaborate) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial begin\n"
             "    #1fs;\n"
             "    #1ps;\n"
             "    #1ns;\n"
             "    #1us;\n"
             "    #1ms;\n"
             "    #1s;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, TimeLiteralInAssignmentElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  realtime r;\n"
             "  initial r = 5ns;\n"
             "endmodule\n"));
}

}  // namespace
