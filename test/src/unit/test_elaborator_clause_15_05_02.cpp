#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §15.5.2: Event wait @(ev) in initial block elaborates.
TEST(EventWaitElaborator, WaitInInitialBlockElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event ev;\n"
      "  initial @(ev);\n"
      "endmodule\n"));
}

// §15.5.2: Event wait with body statement elaborates.
TEST(EventWaitElaborator, WaitWithBodyElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event ev;\n"
      "  logic x;\n"
      "  initial @(ev) x = 1;\n"
      "endmodule\n"));
}

// §15.5.2: Bare @ev syntax (no parentheses) elaborates.
TEST(EventWaitElaborator, BareWaitSyntaxElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event ev;\n"
      "  initial @ev;\n"
      "endmodule\n"));
}

// §15.5.2: Event wait inside begin/end block elaborates.
TEST(EventWaitElaborator, WaitInsideBeginEndElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    @(ev);\n"
      "    result = 42;\n"
      "  end\n"
      "endmodule\n"));
}

}  // namespace
