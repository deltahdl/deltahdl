#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// The clause's CA: rand bytes x and y, bytes v and w, and c1 relating each
// pair, run through the four calls the clause lists.
const char* const kCA =
    "class CA;\n"
    "  rand byte x, y;\n"
    "  byte v, w;\n"
    "  constraint c1 { x < v && y > w; }\n"
    "endclass\n"
    "module t;\n";

// 18.11: called with no arguments, randomize() assigns every rand variable
// and the rest are state; called with arguments, those are the complete set
// of random variables, the rest state, a property not declared rand being
// random for the call. Over the clause's four calls the constraint holds on
// every draw and the unnamed variables keep their values, as the design
// test/src/e2e/inline_random_variable_control.sv runs it.
TEST(InlineRandomVariableControlRun, TheArgumentsAreTheRandomSetOfTheCall) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kCA) +
          "  int none = 0, x_only = 0, v_and_w = 0, w_and_x = 0;\n"
          "  initial begin\n"
          "    CA a = new;\n"
          "    a.v = 100;\n"
          "    a.w = -100;\n"
          "    repeat (32) begin\n"
          "      void'(a.randomize());\n"
          "      if (a.x < 100 && a.y > -100 && a.v == 100 && a.w == -100)\n"
          "        none++;\n"
          "    end\n"
          "    a.y = 50;\n"
          "    repeat (32) begin\n"
          "      void'(a.randomize(x));\n"
          "      if (a.x < 100 && a.y == 50 && a.v == 100 && a.w == -100)\n"
          "        x_only++;\n"
          "    end\n"
          "    a.x = -50;\n"
          "    repeat (32) begin\n"
          "      void'(a.randomize(v, w));\n"
          "      if (a.v > -50 && a.w < 50 && a.x == -50 && a.y == 50)\n"
          "        v_and_w++;\n"
          "    end\n"
          "    a.v = 100;\n"
          "    repeat (32) begin\n"
          "      void'(a.randomize(w, x));\n"
          "      if (a.x < 100 && a.w < 50 && a.y == 50 && a.v == 100)\n"
          "        w_and_x++;\n"
          "    end\n"
          "    $display(\"%0d %0d %0d %0d\", none, x_only, v_and_w, w_and_x);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32 32 32\n");
}

// 18.11: naming a property not declared rand makes it random for the call:
// v, a plain byte, moves between calls of randomize(v, w) while the rand x
// it is drawn above keeps its value.
TEST(InlineRandomVariableControlRun, ANamedNonRandPropertyIsDrawn) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(kCA) +
                     "  int moved = 0, held = 0;\n"
                     "  byte prev;\n"
                     "  initial begin\n"
                     "    CA a = new;\n"
                     "    a.x = -50;\n"
                     "    a.y = 50;\n"
                     "    prev = a.v;\n"
                     "    repeat (32) begin\n"
                     "      void'(a.randomize(v, w));\n"
                     "      if (a.v != prev) moved++;\n"
                     "      if (a.x == -50) held++;\n"
                     "      prev = a.v;\n"
                     "    end\n"
                     "    $display(\"%0d %0d\", moved > 0, held);\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_EQ(out, "1 32\n");
}

// 18.11: the random mode of a local member can be changed only where the
// call has access to it, within its class: a method's bare randomize(secret)
// names the method of the object executing it, succeeds, and draws the
// local secret above the lid on every call.
TEST(InlineRandomVariableControlRun, ALocalMemberIsNamedWithinItsClass) {
  SimFixture f;
  std::string out = RunCapture(
      "class Vault;\n"
      "  local rand byte secret;\n"
      "  byte lid;\n"
      "  constraint lidded { secret > lid; }\n"
      "  function int draw_secret();\n"
      "    return randomize(secret);\n"
      "  endfunction\n"
      "  function byte peek();\n"
      "    return secret;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ok = 0, above = 0;\n"
      "  initial begin\n"
      "    Vault vault = new;\n"
      "    vault.lid = 100;\n"
      "    repeat (32) begin\n"
      "      ok += vault.draw_secret();\n"
      "      if (vault.peek() > 100) above++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", ok, above);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 32\n");
}

}  // namespace
