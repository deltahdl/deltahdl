#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(EventTriggerElaborator, BlockingTriggerElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event ev;\n"
             "  initial -> ev;\n"
             "endmodule\n"));
}

TEST(EventTriggerElaborator, NonblockingTriggerElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event ev;\n"
             "  initial ->> ev;\n"
             "endmodule\n"));
}

TEST(EventTriggerElaborator, NonblockingTriggerWithDelayElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event ev;\n"
             "  initial ->> #5 ev;\n"
             "endmodule\n"));
}

TEST(EventTriggerElaborator, NonblockingTriggerWithEventControlElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event ev;\n"
             "  logic clk;\n"
             "  initial ->> @(posedge clk) ev;\n"
             "endmodule\n"));
}

TEST(EventTriggerElaborator, TriggerAndWaitElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event ev;\n"
             "  initial begin\n"
             "    #5 -> ev;\n"
             "  end\n"
             "  initial begin\n"
             "    @(ev);\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
