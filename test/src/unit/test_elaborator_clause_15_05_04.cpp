#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(WaitOrderElaborator, BasicWaitOrderElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event a, b, c;\n"
      "  initial wait_order(a, b, c);\n"
      "endmodule\n"));
}

TEST(WaitOrderElaborator, WaitOrderWithActionElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event a, b;\n"
      "  initial wait_order(a, b) $display(\"ok\");\n"
      "endmodule\n"));
}

TEST(WaitOrderElaborator, WaitOrderWithElseElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event a, b;\n"
      "  initial\n"
      "    wait_order(a, b) $display(\"ok\");\n"
      "    else $display(\"fail\");\n"
      "endmodule\n"));
}

TEST(WaitOrderElaborator, WaitOrderWithTriggersElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin #1 -> a; #1 -> b; end\n"
      "      wait_order(a, b);\n"
      "    join\n"
      "  end\n"
      "endmodule\n"));
}

}  // namespace
