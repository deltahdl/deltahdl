#include <gtest/gtest.h>

#include "helpers_scheduler.h"

namespace {

// §24.6 with §8.7: a class an anonymous program declares is part of the
// compilation unit's program-wide space, so a program constructs an object of
// it like one of any other class, its constructor setting the property.
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
