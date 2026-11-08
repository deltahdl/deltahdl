#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

const char* const kCA =
    "class CA;\n"
    "  rand byte x, y;\n"
    "  byte v, w;\n"
    "  constraint c1 { x < v && y > w; }\n"
    "endclass\n"
    "module t;\n";

TEST(InlineRandomVariableControlRun, TheArgumentsAreTheRandomSetOfTheCall) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kCA) +
          "  int none = 0, x_only = 0, v_and_w = 0, w_and_x = 0;\n"
          "  initial begin\n"
          "    static CA a = new;\n"
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

TEST(InlineRandomVariableControlRun, ANamedNonRandPropertyIsDrawn) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(kCA) +
                     "  int moved = 0, held = 0;\n"
                     "  byte prev;\n"
                     "  initial begin\n"
                     "    static CA a = new;\n"
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
      "    static Vault vault = new;\n"
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
