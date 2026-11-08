#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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
      "    static C obj = new;\n"
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
      "    static C obj = new;\n"
      "    static Holder h = new;\n"
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

TEST(LocalScopeResolutionRun, LocalReachesTheArgumentPastTheTrialValues) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] x, y;\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  function int f(C obj, int x);\n"
      "    return obj.randomize() with { x + y == local::x; };\n"
      "  endfunction\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (4)\n"
      "      if (f(c, 9) == 1 && c.x + c.y == 9) held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

TEST(LocalScopeResolutionRun, LocalBindsThePropertyOfTheCallersClass) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "endclass\n"
      "class D;\n"
      "  bit [3:0] x = 7;\n"
      "  function int go(C c);\n"
      "    return c.randomize() with { x == local::x; };\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    static D d = new;\n"
      "    repeat (4)\n"
      "      if (d.go(c) == 1 && c.x == 7) held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

TEST(LocalScopeResolutionRun, LocalSuperIsTheCallersSuper) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "  bit [3:0] lim = 1;\n"
      "endclass\n"
      "class B;\n"
      "  bit [3:0] lim = 6;\n"
      "endclass\n"
      "class D extends B;\n"
      "  bit [3:0] lim = 2;\n"
      "  function int go(C c);\n"
      "    return c.randomize() with { x == local::super.lim; };\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    static D d = new;\n"
      "    repeat (4)\n"
      "      if (d.go(c) == 1 && c.x == 6) held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

TEST(LocalScopeResolutionRun, LocalQualifiesTheCallersTypeName) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  typedef bit [3:0] nib_t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    static int big = 21;\n"
      "    repeat (4)\n"
      "      if (c.randomize() with { x == local::nib_t'(big); } == 1 &&\n"
      "          c.x == 5) held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

TEST(LocalScopeResolutionRun, LocalReceiverNamesTheRandomVariable) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (4)\n"
      "      if (c.randomize() with { local::c.x == 5; } == 1 && c.x == 5)\n"
      "        held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

TEST(LocalScopeResolutionRun, LocalBindsTheArgumentOfTheCallersMethod) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "endclass\n"
      "class D;\n"
      "  function int go(C c, int lim);\n"
      "    return c.randomize() with { x == local::lim; };\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    static D d = new;\n"
      "    repeat (4)\n"
      "      if (d.go(c, 11) == 1 && c.x == 11) held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

TEST(LocalScopeResolutionRun, LocalQualifiesATypeOfTheCallersClass) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  typedef bit [3:0] tri_t;\n"
      "  rand bit [7:0] x;\n"
      "endclass\n"
      "class D;\n"
      "  typedef bit [2:0] tri_t;\n"
      "  int big = 13;\n"
      "  function int go(C c);\n"
      "    return c.randomize() with { x == local::tri_t'(local::big); };\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    static D d = new;\n"
      "    repeat (4)\n"
      "      if (d.go(c) == 1 && c.x == 5) held++;\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

}  // namespace
