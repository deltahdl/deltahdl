#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string CountingSet(const std::string& order) {
  return "class B;\n"
         "  rand bit s;\n"
         "  rand bit [31:0] d;\n"
         "  constraint c { s -> d == 0; }\n" +
         order +
         "endclass\n"
         "module t;\n"
         "  int set = 0, wrong = 0;\n"
         "  initial begin\n"
         "    static B o = new;\n"
         "    repeat (512) begin\n"
         "      void'(o.randomize());\n"
         "      if (o.s) set++;\n"
         "      if (o.s && o.d != 0) wrong++;\n"
         "    end\n"
         "    $display(\"%0d %0d\", set > 200 && set < 312, wrong);\n"
         "  end\n"
         "endmodule\n";
}

TEST(VariableOrderingRun, TheUnorderedControlIsAsGoodAsNeverSet) {
  SimFixture f;
  std::string out = RunCapture(
      "class B;\n"
      "  rand bit s;\n"
      "  rand bit [31:0] d;\n"
      "  constraint c { s -> d == 0; }\n"
      "endclass\n"
      "module t;\n"
      "  int set = 0;\n"
      "  initial begin\n"
      "    static B o = new;\n"
      "    repeat (512) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.s) set++;\n"
      "    end\n"
      "    $display(\"%0d\", set);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

TEST(VariableOrderingRun, TheOrderedControlIsSetHalfTheTime) {
  SimFixture f;
  std::string out =
      RunCapture(CountingSet("  constraint order { solve s before d; }\n"), f);
  EXPECT_EQ(out, "1 0\n");
}

TEST(VariableOrderingRun, AnOrderingNeverFailsTheSolve) {
  SimFixture f;
  std::string out = RunCapture(
      "class B;\n"
      "  rand bit [3:0] x;\n"
      "  rand bit [3:0] y;\n"
      "  constraint k { x == 0; x < y; }\n"
      "  constraint order { solve y before x; }\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0;\n"
      "  initial begin\n"
      "    static B o = new;\n"
      "    repeat (64) begin\n"
      "      if (o.randomize() && o.x == 0 && o.y > 0) held++;\n"
      "    end\n"
      "    $display(\"%0d\", held);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "64\n");
}

}  // namespace
