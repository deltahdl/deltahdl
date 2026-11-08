#include <gtest/gtest.h>

#include "helpers_scheduler.h"

namespace {

TEST(AnonymousProgramSim, ClassDeclaredInAnAnonymousProgramIsConstructed) {
  auto v = RunAndGet(
      "program;\n"
      "  class Box; int v; function new(int x); v = x; endfunction endclass\n"
      "endprogram\n"
      "module top;\n"
      "  int result;\n"
      "  program p;\n"
      "    Box b;\n"
      "    initial begin b = new(19); result = b.v + 1; end\n"
      "  endprogram\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

}  // namespace
