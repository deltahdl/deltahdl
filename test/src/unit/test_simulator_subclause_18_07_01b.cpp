#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// 18.7.1: the clause's F(C obj, integer x), obj.randomize() with { x <
// local::x; }: the bare x binds to the property of C, the object being
// randomized, and local::x bypasses that class and binds to the argument,
// so over 32 draws obj.x lies from 0 below the argument 40 on every one, as
// the design test/src/e2e/local_scope_resolution.sv runs it.
TEST(LocalScopeResolutionRun, LocalBindsTheArgumentTheBareNameHides) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand integer x;\n"
      "endclass\n"
      "module t;\n"
      "  int success = 0, below = 0;\n"
      "  function int F(C obj, integer x);\n"
      "    F = obj.randomize() with { x < local::x; x >= 0; };\n"
      "  endfunction\n"
      "  initial begin\n"
      "    C obj = new;\n"
      "    repeat (32) begin\n"
      "      if (F(obj, 40) == 1) success++;\n"
      "      if (obj.x >= 0 && obj.x < 40) below++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", success, below);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32\n");
}

// 18.7.1: local::this binds to the scope containing the call, so in a
// Holder's method randomizing a C under x < local::this.limit the limit is
// the Holder's 12, not a member of the C the block's own this names: over
// 32 draws obj.x lies from 0 below 12 on every one.
TEST(LocalScopeResolutionRun, LocalThisIsTheCallersThis) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand integer x;\n"
      "endclass\n"
      "class Holder;\n"
      "  rand integer x;\n"
      "  int limit = 12;\n"
      "  function int bound(C obj);\n"
      "    return obj.randomize() with { x < local::this.limit; x >= 0; };\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int success = 0, below = 0;\n"
      "  initial begin\n"
      "    C obj = new;\n"
      "    Holder h = new;\n"
      "    repeat (32) begin\n"
      "      if (h.bound(obj) == 1) success++;\n"
      "      if (obj.x >= 0 && obj.x < 12) below++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", success, below);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32\n");
}

}  // namespace
