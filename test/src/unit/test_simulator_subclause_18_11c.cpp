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

std::string InModule(const std::string& classes, const std::string& body) {
  return classes +
         "module t;\n"
         "  initial begin\n" +
         body +
         "  end\n"
         "endmodule\n";
}

TEST(InlineRandomControlCases, ANullCallInAMethodChecksTheObject) {
  EXPECT_EQ(RunSrc(InModule("class C;\n"
                            "  rand bit [3:0] x;\n"
                            "  constraint c { x < 5; }\n"
                            "  function int bare();\n"
                            "    return randomize(null);\n"
                            "  endfunction\n"
                            "  function int self();\n"
                            "    return this.randomize(null);\n"
                            "  endfunction\n"
                            "endclass\n",
                            "    static C o = new;\n"
                            "    o.x = 3;\n"
                            "    $display(\"%0d %0d %0d\", o.bare(), o.self(), "
                            "o.x);\n"
                            "    o.x = 9;\n"
                            "    $display(\"%0d %0d %0d\", o.bare(), o.self(), "
                            "o.x);\n")),
            "1 1 3\n0 0 9\n");
}

TEST(InlineRandomControlCases, AnotherInstancesLocalMemberIsDrawn) {
  EXPECT_EQ(RunSrc(InModule("class C;\n"
                            "  local rand bit [7:0] x;\n"
                            "  constraint c { x == 21; }\n"
                            "  function int roll(C b);\n"
                            "    return b.randomize(x);\n"
                            "  endfunction\n"
                            "  function int get();\n"
                            "    return x;\n"
                            "  endfunction\n"
                            "endclass\n",
                            "    static C a = new;\n"
                            "    static C b = new;\n"
                            "    $display(\"%0d %0d %0d\", a.roll(b), b.get(), "
                            "a.get());\n")),
            "1 21 0\n");
}

TEST(InlineRandomControlCases, ABaseProtectedMemberIsDrawnInADerivedMethod) {
  EXPECT_EQ(RunSrc(InModule("class B;\n"
                            "  protected rand bit [7:0] x;\n"
                            "  constraint c { x == 33; }\n"
                            "endclass\n"
                            "class D extends B;\n"
                            "  function int roll();\n"
                            "    return randomize(x);\n"
                            "  endfunction\n"
                            "  function int get();\n"
                            "    return x;\n"
                            "  endfunction\n"
                            "endclass\n",
                            "    static D d = new;\n"
                            "    $display(\"%0d %0d\", d.roll(), d.get());\n")),
            "1 33\n");
}

TEST(InlineRandomControlCases, AVariableLeftOutIsRandomAgainNextCall) {
  EXPECT_EQ(RunSrc(InModule("class C;\n"
                            "  rand bit [3:0] x, y;\n"
                            "  constraint c { y != 0; }\n"
                            "endclass\n",
                            "    static C o = new;\n"
                            "    static int moved = 0;\n"
                            "    o.y = 0;\n"
                            "    void'(o.randomize(x));\n"
                            "    $display(\"%0d\", o.y);\n"
                            "    void'(o.randomize());\n"
                            "    $display(\"%0d\", o.y != 0);\n")),
            "0\n1\n");
}

TEST(InlineRandomControlCases, NamingAnInactiveVariableLeavesItsModeOff) {
  EXPECT_EQ(RunSrc(InModule("class C;\n"
                            "  rand bit [3:0] x, v;\n"
                            "  constraint c { v == 6; }\n"
                            "endclass\n",
                            "    static C o = new;\n"
                            "    int ok;\n"
                            "    o.v.rand_mode(0);\n"
                            "    ok = o.randomize(x, v);\n"
                            "    $display(\"%0d %0d %0d\", ok, o.v, "
                            "o.v.rand_mode());\n")),
            "1 6 0\n");
}

TEST(InlineRandomControlCases, AnInheritedPropertyNamedIsDrawnAndTheRestHeld) {
  EXPECT_EQ(RunSrc(InModule("class B;\n"
                            "  bit [7:0] y;\n"
                            "  constraint cy { y == 61; }\n"
                            "endclass\n"
                            "class C extends B;\n"
                            "  rand bit [7:0] x;\n"
                            "endclass\n",
                            "    static C o = new;\n"
                            "    int ok;\n"
                            "    o.x = 2;\n"
                            "    ok = o.randomize(y);\n"
                            "    $display(\"%0d %0d %0d\", ok, o.y, o.x);\n")),
            "1 61 2\n");
}

std::string ArrayNamed(const std::string& qualifier, const std::string& args) {
  return InModule(
      "class C;\n"
      "  " +
          qualifier +
          "bit [7:0] b[3];\n"
          "  rand bit [7:0] x;\n"
          "  constraint c { foreach (b[i]) b[i] == i + 20; }\n"
          "endclass\n",
      "    static C o = new;\n"
      "    int ok;\n"
      "    o.x = 5;\n"
      "    ok = o.randomize(" +
          args +
          ");\n"
          "    $display(\"%0d %0d %0d %0d %0d\", ok, o.b[0], "
          "o.b[1], o.b[2], o.x);\n");
}

TEST(InlineRandomControlCases, DISABLED_ARandUnpackedArrayNamedIsDrawn) {
  EXPECT_EQ(RunSrc(ArrayNamed("rand ", "b")), "1 20 21 22 5\n");
}

TEST(InlineRandomControlCases, DISABLED_ANonRandUnpackedArrayNamedIsDrawn) {
  EXPECT_EQ(RunSrc(ArrayNamed("", "b")), "1 20 21 22 5\n");
}

TEST(InlineRandomControlCases, DISABLED_AClassHandleNamedRandomizesItsObject) {
  EXPECT_EQ(RunSrc(InModule("class S;\n"
                            "  rand bit [7:0] v;\n"
                            "  constraint c { v == 77; }\n"
                            "endclass\n"
                            "class C;\n"
                            "  S s = new;\n"
                            "  rand bit [7:0] x;\n"
                            "endclass\n",
                            "    static C o = new;\n"
                            "    int ok;\n"
                            "    ok = o.randomize(s);\n"
                            "    $display(\"%0d %0d\", ok, o.s.v);\n")),
            "1 77\n");
}

TEST(InlineRandomControlCases, AStaticPropertyNamedIsDrawnAndTheRestHeld) {
  EXPECT_EQ(RunSrc(InModule("class C;\n"
                            "  static rand bit [7:0] s;\n"
                            "  rand bit [7:0] y;\n"
                            "  constraint c { s == 42; }\n"
                            "endclass\n",
                            "    static C o = new;\n"
                            "    int ok;\n"
                            "    o.y = 7;\n"
                            "    ok = o.randomize(s);\n"
                            "    $display(\"%0d %0d %0d\", ok, C::s, o.y);\n")),
            "1 42 7\n");
}

TEST(InlineRandomControlCases, ACallInAProgramDrawsTheNamedVariable) {
  EXPECT_EQ(RunAllTops("program p;\n"
                       "  class C;\n"
                       "    rand bit [7:0] x, y;\n"
                       "    constraint c { x == 9; }\n"
                       "  endclass\n"
                       "  initial begin\n"
                       "    static C o = new;\n"
                       "    int ok;\n"
                       "    o.y = 4;\n"
                       "    ok = o.randomize(x);\n"
                       "    $display(\"%0d %0d %0d\", ok, o.x, o.y);\n"
                       "  end\n"
                       "endprogram\n"),
            "1 9 4\n");
}

TEST(InlineRandomControlCases, AnArgumentNamesThePropertyNotTheCallersName) {
  EXPECT_EQ(RunSrc("class C;\n"
                   "  bit [7:0] q;\n"
                   "  constraint c { q == 9; }\n"
                   "endclass\n"
                   "module t;\n"
                   "  bit [7:0] q = 1;\n"
                   "  initial begin\n"
                   "    static C o = new;\n"
                   "    void'(o.randomize(q));\n"
                   "    $display(\"%0d %0d\", o.q, q);\n"
                   "  end\n"
                   "endmodule\n"),
            "9 1\n");
}

}  // namespace
