#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunSrc(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

std::string RunAllTops(const std::string& src) {
  SimFixture f;
  return RunCaptureAllTops(src, f);
}

const char kClassX[] =
    "class C;\n"
    "  rand bit [7:0] x;\n"
    "endclass\n";

TEST(InlineConstraintCases, ACallNamingOneVariableDrawsItUnderTheBlock) {
  EXPECT_EQ(RunSrc("class C;\n"
                   "  rand int x, y;\n"
                   "endclass\n"
                   "module t;\n"
                   "  initial begin\n"
                   "    static C c = new;\n"
                   "    int ok;\n"
                   "    c.y = 7;\n"
                   "    ok = c.randomize(x) with { x == y + 1; };\n"
                   "    $display(\"%0d %0d %0d\", ok, c.x, c.y);\n"
                   "  end\n"
                   "endmodule\n"),
            "1 8 7\n");
}

TEST(InlineConstraintCases, ACallNamingTwoVariablesHoldsTheRest) {
  EXPECT_EQ(RunSrc("class C;\n"
                   "  rand int x, y, z;\n"
                   "endclass\n"
                   "module t;\n"
                   "  initial begin\n"
                   "    static C c = new;\n"
                   "    int ok;\n"
                   "    c.z = 9;\n"
                   "    ok = c.randomize(x, y) with { x == y + 1; y == 4; };\n"
                   "    $display(\"%0d %0d %0d %0d\", ok, c.x, c.y, c.z);\n"
                   "  end\n"
                   "endmodule\n"),
            "1 5 4 9\n");
}

TEST(InlineConstraintCases, AnAutomaticLocalIsReadWhenTheObjectLacksIt) {
  EXPECT_EQ(RunSrc(std::string(kClassX) +
                   "module t;\n"
                   "  initial begin\n"
                   "    automatic int w = 3;\n"
                   "    automatic C c = new;\n"
                   "    void'(c.randomize() with { x == w; });\n"
                   "    $display(\"%0d\", c.x);\n"
                   "  end\n"
                   "endmodule\n"),
            "3\n");
}

TEST(InlineConstraintCases, AnInheritedMemberHidesTheCallersVariable) {
  EXPECT_EQ(RunSrc("class B;\n"
                   "  int k = 3;\n"
                   "endclass\n"
                   "class D extends B;\n"
                   "  rand int x;\n"
                   "endclass\n"
                   "module t;\n"
                   "  int k = 9;\n"
                   "  initial begin\n"
                   "    static D d = new;\n"
                   "    void'(d.randomize() with { x == k; });\n"
                   "    $display(\"%0d\", d.x);\n"
                   "  end\n"
                   "endmodule\n"),
            "3\n");
}

TEST(InlineConstraintCases, DISABLED_TheHandlesDeclaredClassIsSearched) {
  EXPECT_EQ(RunSrc("class B;\n"
                   "  rand int x;\n"
                   "endclass\n"
                   "class D extends B;\n"
                   "  int y = 1;\n"
                   "endclass\n"
                   "module t;\n"
                   "  int y = 8;\n"
                   "  initial begin\n"
                   "    static D d = new;\n"
                   "    static B b = d;\n"
                   "    void'(b.randomize() with { x == y; });\n"
                   "    $display(\"%0d\", b.x);\n"
                   "  end\n"
                   "endmodule\n"),
            "8\n");
}

TEST(InlineConstraintCases, AStaticFunctionReadsItsFormalPastTheObject) {
  EXPECT_EQ(RunSrc("class C;\n"
                   "  rand bit [7:0] x;\n"
                   "  constraint c { x inside {[1:2]}; }\n"
                   "  static function int drive(C h, int want);\n"
                   "    if (h.randomize() with { x == want; } != 1) return 1;\n"
                   "    return h.x != want;\n"
                   "  endfunction\n"
                   "endclass\n"
                   "module t;\n"
                   "  C c = new;\n"
                   "  int bad = 0;\n"
                   "  initial begin\n"
                   "    repeat (10) begin\n"
                   "      bad += C::drive(c, 1);\n"
                   "      bad += C::drive(c, 2);\n"
                   "    end\n"
                   "    $display(\"bad %0d\", bad);\n"
                   "  end\n"
                   "endmodule\n"),
            "bad 0\n");
}

TEST(InlineConstraintCases, AThisNameInAnotherClassesMethodReadsTheObjects) {
  EXPECT_EQ(RunSrc("class C;\n"
                   "  rand bit [7:0] x;\n"
                   "  int limit = 10;\n"
                   "endclass\n"
                   "class H;\n"
                   "  int limit = 100;\n"
                   "  function int go(C obj);\n"
                   "    return obj.randomize() with { x < this.limit; };\n"
                   "  endfunction\n"
                   "endclass\n"
                   "module t;\n"
                   "  int ok = 0, below = 0;\n"
                   "  initial begin\n"
                   "    static C c = new;\n"
                   "    static H h = new;\n"
                   "    repeat (32) begin\n"
                   "      if (h.go(c) == 1) ok++;\n"
                   "      if (c.x < 10) below++;\n"
                   "    end\n"
                   "    $display(\"%0d %0d\", ok, below);\n"
                   "  end\n"
                   "endmodule\n"),
            "32 32\n");
}

TEST(InlineConstraintCases, ASuperNameReadsTheBasesMemberOverTheObjects) {
  EXPECT_EQ(RunSrc("class B;\n"
                   "  int lim = 5;\n"
                   "endclass\n"
                   "class D extends B;\n"
                   "  rand int x;\n"
                   "  int lim = 50;\n"
                   "endclass\n"
                   "module t;\n"
                   "  initial begin\n"
                   "    static D d = new;\n"
                   "    void'(d.randomize() with { x == super.lim; });\n"
                   "    $display(\"%0d\", d.x);\n"
                   "  end\n"
                   "endmodule\n"),
            "5\n");
}

TEST(InlineConstraintCases, ADottedHeadTheObjectLacksResolvesInTheCaller) {
  EXPECT_EQ(RunSrc("class Box;\n"
                   "  int v;\n"
                   "endclass\n" +
                   std::string(kClassX) +
                   "module t;\n"
                   "  initial begin\n"
                   "    static Box h = new;\n"
                   "    static C c = new;\n"
                   "    h.v = 2;\n"
                   "    void'(c.randomize() with { x == h.v; });\n"
                   "    $display(\"%0d\", c.x);\n"
                   "  end\n"
                   "endmodule\n"),
            "2\n");
}

TEST(InlineConstraintCases, AHierarchicalNameReachesTheEnclosingModule) {
  EXPECT_EQ(RunSrc(std::string(kClassX) +
                   "module t;\n"
                   "  int v = 6;\n"
                   "  initial begin\n"
                   "    static C c = new;\n"
                   "    void'(c.randomize() with { x == t.v; });\n"
                   "    $display(\"%0d\", c.x);\n"
                   "  end\n"
                   "endmodule\n"),
            "6\n");
}

TEST(InlineConstraintCases, AnInheritedConstraintJoinsTheBlock) {
  EXPECT_EQ(RunSrc("class B;\n"
                   "  rand bit [7:0] x;\n"
                   "  constraint c { x > 200; }\n"
                   "endclass\n"
                   "class D extends B;\n"
                   "endclass\n"
                   "module t;\n"
                   "  initial begin\n"
                   "    static D d = new;\n"
                   "    int ok;\n"
                   "    ok = d.randomize() with { x < 202; };\n"
                   "    $display(\"%0d %0d\", ok, d.x);\n"
                   "  end\n"
                   "endmodule\n"),
            "1 201\n");
}

TEST(InlineConstraintCases, ALaterPlainCallIsNotHeldByTheBlock) {
  EXPECT_EQ(RunSrc("class C;\n"
                   "  rand bit [3:0] x;\n"
                   "endclass\n"
                   "module t;\n"
                   "  int other = 0;\n"
                   "  initial begin\n"
                   "    static C c = new;\n"
                   "    void'(c.randomize() with { x == 3; });\n"
                   "    $display(\"%0d\", c.x);\n"
                   "    repeat (40) begin\n"
                   "      void'(c.randomize());\n"
                   "      if (c.x != 3) other++;\n"
                   "    end\n"
                   "    $display(\"%0d\", other > 0);\n"
                   "  end\n"
                   "endmodule\n"),
            "3\n1\n");
}

TEST(InlineConstraintCases, ACallInAProgramInitialBlock) {
  EXPECT_EQ(RunAllTops(std::string(kClassX) +
                       "program p;\n"
                       "  initial begin\n"
                       "    static C c = new;\n"
                       "    void'(c.randomize() with { x == 12; });\n"
                       "    $display(\"%0d\", c.x);\n"
                       "  end\n"
                       "endprogram\n"),
            "12\n");
}

TEST(InlineConstraintCases, ACallInAPackageFunction) {
  EXPECT_EQ(RunSrc("package q;\n"
                   "  class C;\n"
                   "    rand bit [7:0] x;\n"
                   "  endclass\n"
                   "  function automatic int draw(int want);\n"
                   "    C c = new;\n"
                   "    void'(c.randomize() with { x == want; });\n"
                   "    return c.x;\n"
                   "  endfunction\n"
                   "endpackage\n"
                   "module t;\n"
                   "  initial $display(\"%0d\", q::draw(13));\n"
                   "endmodule\n"),
            "13\n");
}

TEST(InlineConstraintCases, ACallInACompilationUnitFunction) {
  EXPECT_EQ(RunSrc(std::string(kClassX) +
                   "function automatic int draw(int want);\n"
                   "  C c = new;\n"
                   "  void'(c.randomize() with { x == want; });\n"
                   "  return c.x;\n"
                   "endfunction\n"
                   "module t;\n"
                   "  initial $display(\"%0d\", draw(14));\n"
                   "endmodule\n"),
            "14\n");
}

TEST(InlineConstraintCases,
     ACallInAnInterfaceFunctionCalledThroughItsInstance) {
  EXPECT_EQ(RunSrc(std::string(kClassX) +
                   "interface ifc;\n"
                   "  int base = 15;\n"
                   "  function automatic int draw();\n"
                   "    C c = new;\n"
                   "    void'(c.randomize() with { x == base; });\n"
                   "    return c.x;\n"
                   "  endfunction\n"
                   "endinterface\n"
                   "module t;\n"
                   "  ifc ifc_inst();\n"
                   "  initial $display(\"%0d\", ifc_inst.draw());\n"
                   "endmodule\n"),
            "15\n");
}

TEST(InlineConstraintCases, ACallAsASystemTaskArgument) {
  EXPECT_EQ(RunSrc(std::string(kClassX) +
                   "module t;\n"
                   "  initial begin\n"
                   "    static C c = new;\n"
                   "    $display(\"%0d\", c.randomize() with { x == 16; });\n"
                   "    $display(\"%0d\", c.x);\n"
                   "  end\n"
                   "endmodule\n"),
            "1\n16\n");
}

TEST(InlineConstraintCases, AUniqueGroupDrawsDistinctValues) {
  EXPECT_EQ(
      RunSrc("class C;\n"
             "  rand bit [1:0] a, b, c;\n"
             "endclass\n"
             "module t;\n"
             "  int ok = 0, distinct = 0;\n"
             "  initial begin\n"
             "    static C o = new;\n"
             "    repeat (50) begin\n"
             "      if (o.randomize() with { unique { a, b, c }; }) ok++;\n"
             "      if (o.a != o.b && o.b != o.c && o.a != o.c) distinct++;\n"
             "    end\n"
             "    $display(\"%0d %0d\", ok, distinct);\n"
             "  end\n"
             "endmodule\n"),
      "50 50\n");
}

TEST(InlineConstraintCases, DISABLED_ASolveBeforeOrderingKeepsTheBlock) {
  EXPECT_EQ(RunSrc("class C;\n"
                   "  rand bit [3:0] x, y;\n"
                   "endclass\n"
                   "module t;\n"
                   "  int ok = 0, held = 0;\n"
                   "  initial begin\n"
                   "    static C c = new;\n"
                   "    repeat (64) begin\n"
                   "      if (c.randomize() with {\n"
                   "            solve x before y;\n"
                   "            x == 1;\n"
                   "            y == x + 1;\n"
                   "          })\n"
                   "        ok++;\n"
                   "      if (c.x == 1 && c.y == 2) held++;\n"
                   "    end\n"
                   "    $display(\"%0d %0d\", ok, held);\n"
                   "  end\n"
                   "endmodule\n"),
            "64 64\n");
}

TEST(InlineConstraintCases, TwoListedNamesBothBindIntoTheObject) {
  EXPECT_EQ(
      RunSrc("class C;\n"
             "  rand int x, y;\n"
             "endclass\n"
             "module t;\n"
             "  function int F(C obj, int y);\n"
             "    return obj.randomize() with (x, y) { x == 2; y == x + 1; "
             "};\n"
             "  endfunction\n"
             "  initial begin\n"
             "    static C c = new;\n"
             "    int ok;\n"
             "    ok = F(c, 50);\n"
             "    $display(\"%0d %0d %0d\", ok, c.x, c.y);\n"
             "  end\n"
             "endmodule\n"),
      "1 2 3\n");
}

TEST(InlineConstraintCases, AListedDottedHeadBindsIntoTheObject) {
  EXPECT_EQ(RunSrc("class Box;\n"
                   "  int v;\n"
                   "endclass\n"
                   "class C;\n"
                   "  rand int x;\n"
                   "  Box h = new;\n"
                   "endclass\n"
                   "module t;\n"
                   "  initial begin\n"
                   "    static Box h = new;\n"
                   "    static C c = new;\n"
                   "    h.v = 4;\n"
                   "    c.h.v = 9;\n"
                   "    void'(c.randomize() with (x, h) { x == h.v; });\n"
                   "    $display(\"%0d\", c.x);\n"
                   "  end\n"
                   "endmodule\n"),
            "9\n");
}

}  // namespace
