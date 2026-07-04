#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(EventTriggeredElaborator, WaitTriggeredElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event ev;\n"
             "  initial wait(ev.triggered);\n"
             "endmodule\n"));
}

TEST(EventTriggeredElaborator, ForkTriggerAndWaitTriggeredElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event blast;\n"
             "  initial begin\n"
             "    fork\n"
             "      -> blast;\n"
             "      wait(blast.triggered);\n"
             "    join\n"
             "  end\n"
             "endmodule\n"));
}

TEST(EventTriggeredElaborator, TriggeredCallFormElaborates) {
  // §15.5.3: the parenthesized call form of the triggered method is a
  // bit-valued expression, so it elaborates as the right-hand side of an
  // assignment without being flagged as an unknown function call.
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event ev;\n"
             "  logic b;\n"
             "  initial b = ev.triggered();\n"
             "endmodule\n"));
}

}  // namespace
