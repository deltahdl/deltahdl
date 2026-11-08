#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

const char* const kGatedHead =
    "class C;\n"
    "  rand bit p;\n"
    "  rand bit q;\n"
    "  constraint c_1 { p -> soft q; }\n"
    "  constraint c_2 { soft p; }\n";

TEST(DisablingSoftConstraintsRun, TheGateOfASoftConsequentIsNoReference) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kGatedHead) +
          "  constraint c_3 { disable soft p; }\n"
          "endclass\n"
          "module t;\n"
          "  int sets = 0, gated = 0;\n"
          "  initial begin\n"
          "    static C c = new;\n"
          "    repeat (32) begin\n"
          "      void'(c.randomize());\n"
          "      if (c.p) sets++;\n"
          "      if (!c.p || c.q) gated++;\n"
          "    end\n"
          "    $display(\"%0d %0d\", sets > 0 && sets < 32, gated);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "1 32\n");
}

TEST(DisablingSoftConstraintsRun, ADirectiveOnTheConsequentDiscardsTheGated) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(kGatedHead) +
                     "  constraint c_3 { disable soft q; }\n"
                     "endclass\n"
                     "module t;\n"
                     "  int sets = 0, clears = 0;\n"
                     "  initial begin\n"
                     "    static C c = new;\n"
                     "    repeat (32) begin\n"
                     "      void'(c.randomize());\n"
                     "      if (c.p) sets++;\n"
                     "      if (!c.q) clears++;\n"
                     "    end\n"
                     "    $display(\"%0d %0d\", sets, clears > 0);\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_EQ(out, "32 1\n");
}

TEST(DisablingSoftConstraintsRun, TheClausesADrawsTheLaterMembership) {
  SimFixture f;
  std::string out = RunCapture(
      "class A;\n"
      "  rand int x;\n"
      "  constraint A1 { soft x == 3; }\n"
      "  constraint A2 { disable soft x; }\n"
      "  constraint A3 { soft x inside {1, 2}; }\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0, ones = 0, twos = 0;\n"
      "  initial begin\n"
      "    static A a = new;\n"
      "    repeat (32) begin\n"
      "      void'(a.randomize());\n"
      "      if (a.x == 1 || a.x == 2) held++;\n"
      "      if (a.x == 1) ones++;\n"
      "      if (a.x == 2) twos++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", held, ones > 0 && twos > 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 1\n");
}

}  // namespace
