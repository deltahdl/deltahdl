#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(EventTriggeredElaborator, WaitTriggeredElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event ev;\n"
      "  initial wait(ev.triggered);\n"
      "endmodule\n"));
}

TEST(EventTriggeredElaborator, WaitTriggeredWithBodyElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event ev;\n"
      "  initial wait(ev.triggered) $display(\"done\");\n"
      "endmodule\n"));
}

TEST(EventTriggeredElaborator, ForkTriggerAndWaitTriggeredElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event blast;\n"
      "  initial begin\n"
      "    fork\n"
      "      -> blast;\n"
      "      wait(blast.triggered);\n"
      "    join\n"
      "  end\n"
      "endmodule\n"));
}


}  // namespace
