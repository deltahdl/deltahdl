#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// 18.7: the clause's C1 and C2. In doit's f.randomize() with block x is
// the member of C1, hiding both the member of C2 and the argument, y is the
// member of C2 and z the argument: with the member y at 10 and z at 5 every
// one of 32 draws leaves f.x from 10 below 15, whatever the argument x, as
// the design test/src/e2e/inline_constraints.sv runs it.
TEST(InlineConstraintsRun, TheBlockResolvesInTheObjectThenTheCallersScope) {
  SimFixture f;
  std::string out = RunCapture(
      "class C1;\n"
      "  rand integer x;\n"
      "endclass\n"
      "class C2;\n"
      "  integer x;\n"
      "  integer y;\n"
      "  function int doit(C1 f, integer x, integer z);\n"
      "    return f.randomize() with { x < y + z; x >= y; };\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int success = 0, held = 0;\n"
      "  initial begin\n"
      "    C1 f = new;\n"
      "    C2 c2 = new;\n"
      "    c2.x = -1000;\n"
      "    c2.y = 10;\n"
      "    repeat (32) begin\n"
      "      if (c2.doit(f, -1000, 5) == 1) success++;\n"
      "      if (f.x >= 10 && f.x < 15) held++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", success, held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32\n");
}

// 18.7: the clause's restricted block, obj.randomize() with (x) { x < y; }
// in a function F(C obj, integer y): only x resolves into obj, so y is the
// argument though obj declares a y, and over 32 draws obj.x lies below the
// argument 20 on every one.
TEST(InlineConstraintsRun, ARestrictedBlockResolvesOnlyTheListedNames) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand integer x;\n"
      "  rand integer y;\n"
      "endclass\n"
      "module t;\n"
      "  int success = 0, below = 0;\n"
      "  function int F(C obj, integer y);\n"
      "    F = obj.randomize() with (x) { x < y; };\n"
      "  endfunction\n"
      "  initial begin\n"
      "    C obj = new;\n"
      "    repeat (32) begin\n"
      "      if (F(obj, 20) == 1) success++;\n"
      "      if (obj.x < 20) below++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", success, below);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32\n");
}

}  // namespace
