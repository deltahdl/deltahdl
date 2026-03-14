#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §15.5.1: Blocking event trigger in initial block elaborates.
TEST(EventTriggerElaborator, BlockingTriggerElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event ev;\n"
      "  initial -> ev;\n"
      "endmodule\n"));
}

// §15.5.1: Nonblocking event trigger elaborates.
TEST(EventTriggerElaborator, NonblockingTriggerElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event ev;\n"
      "  initial ->> ev;\n"
      "endmodule\n"));
}

// §15.5.1: Nonblocking trigger with delay elaborates.
TEST(EventTriggerElaborator, NonblockingTriggerWithDelayElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event ev;\n"
      "  initial ->> #5 ev;\n"
      "endmodule\n"));
}

// §15.5.1: Event trigger with event declaration and wait elaborates.
TEST(EventTriggerElaborator, TriggerAndWaitElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
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
