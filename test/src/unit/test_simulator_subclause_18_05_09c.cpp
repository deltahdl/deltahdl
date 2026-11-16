#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunSrc(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

std::string ObjectOrdering(const std::string& class_tail,
                           const std::string& after, const std::string& call) {
  return "class B;\n"
         "  rand bit s;\n"
         "  rand bit [31:0] d;\n"
         "  constraint c { s -> d == 0; }\n" +
         class_tail + "endclass\n" + after +
         "module t;\n"
         "  int set = 0, wrong = 0;\n"
         "  initial begin\n"
         "    static B o = new;\n"
         "    repeat (512) begin\n"
         "      if (!(" +
         call +
         ")) wrong++;\n"
         "      if (o.s) set++;\n"
         "      if (o.s && o.d != 0) wrong++;\n"
         "    end\n"
         "    $display(\"%0d %0d\", set > 200 && set < 312, wrong);\n"
         "  end\n"
         "endmodule\n";
}

TEST(VariableOrderingCases, AnOutOfBlockOrderingSetsTheControlHalfTheTime) {
  EXPECT_EQ(RunSrc(ObjectOrdering("  constraint o;\n",
                                  "constraint B::o { solve s before d; }\n",
                                  "o.randomize()")),
            "1 0\n");
}

TEST(VariableOrderingCases, AnInlineOrderingSetsTheControlHalfTheTime) {
  EXPECT_EQ(RunSrc(ObjectOrdering("", "",
                                  "o.randomize() with { solve s before d; }")),
            "1 0\n");
}

TEST(VariableOrderingCases,
     DISABLED_AScopeRandomizeOrderingSetsTheControlHalfTheTime) {
  EXPECT_EQ(RunSrc("module t;\n"
                   "  bit s;\n"
                   "  bit [31:0] d;\n"
                   "  int set = 0, wrong = 0;\n"
                   "  initial begin\n"
                   "    repeat (512) begin\n"
                   "      if (!std::randomize(s, d) with { s -> d == 0; "
                   "solve s before d; }) wrong++;\n"
                   "      if (s) set++;\n"
                   "      if (s && d != 0) wrong++;\n"
                   "    end\n"
                   "    $display(\"%0d %0d\", set > 200 && set < 312, wrong);\n"
                   "  end\n"
                   "endmodule\n"),
            "1 0\n");
}

const char* const kAgainstTheGrain = "x == 0; x < y; solve y before x;";

TEST(VariableOrderingCases, AnInlineOrderingAgainstTheGrainNeverFails) {
  EXPECT_EQ(RunSrc(std::string("class C; rand bit [3:0] x, y; endclass\n"
                               "module t;\n"
                               "  int n, held = 0;\n"
                               "  initial begin\n"
                               "    static C o = new;\n"
                               "    for (n = 0; n < 32; n++)\n"
                               "      if (o.randomize() with { ") +
                   kAgainstTheGrain +
                   " } && o.x == 0 && o.y > 0) held++;\n"
                   "    $display(\"%0d\", held);\n"
                   "  end\n"
                   "endmodule\n"),
            "32\n");
}

TEST(VariableOrderingCases, AScopeRandomizeOrderingAgainstTheGrainNeverFails) {
  EXPECT_EQ(RunSrc(std::string("module t;\n"
                               "  bit [3:0] x, y;\n"
                               "  int n, held = 0;\n"
                               "  initial begin\n"
                               "    for (n = 0; n < 32; n++)\n"
                               "      if (std::randomize(x, y) with { ") +
                   kAgainstTheGrain +
                   " } && x == 0 && y > 0) held++;\n"
                   "    $display(\"%0d\", held);\n"
                   "  end\n"
                   "endmodule\n"),
            "32\n");
}

}  // namespace
