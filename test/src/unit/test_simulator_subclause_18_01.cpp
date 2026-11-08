#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string Design(const std::string& body) {
  return "class Bus;\n"
         "  rand bit [15:0] addr;\n"
         "  rand bit [31:0] data;\n"
         "  constraint word_align { addr[1:0] == 2'b0; }\n"
         "endclass\n"
         "module t;\n"
         "  initial begin\n"
         "    static Bus bus = new;\n"
         "    static Bus other = new;\n"
         "    int v;\n"
         "    int taken;\n"
         "    bit ok;\n" +
         body +
         "  end\n"
         "endmodule\n";
}

TEST(ConstrainedRandomOverview, VariablesConstraintsAndMethods) {
  SimFixture f;
  std::string out =
      RunCapture(Design("    ok = bus.randomize();\n"
                        "    $display(\"%0d %0d\", ok, bus.addr[1:0]);\n"
                        "    ok = bus.randomize() with { addr == 8; };\n"
                        "    $display(\"%0d\", ok && bus.addr == 8);\n"),
                 f);
  EXPECT_EQ(out, "1 0\n1\n");
}

TEST(ConstrainedRandomOverview, DisablingRandomizationAndConstraints) {
  SimFixture f;
  std::string out =
      RunCapture(Design("    bus.data.rand_mode(0);\n"
                        "    bus.data = 99;\n"
                        "    void'(bus.randomize());\n"
                        "    $display(\"%0d\", bus.data);\n"
                        "    bus.word_align.constraint_mode(0);\n"
                        "    ok = bus.randomize() with { addr == 3; };\n"
                        "    $display(\"%0d\", ok && bus.addr == 3);\n"),
                 f);
  EXPECT_EQ(out, "99\n1\n");
}

TEST(ConstrainedRandomOverview, ScopeSeedingRandcaseAndRandsequence) {
  SimFixture f;
  std::string out = RunCapture(
      Design("    ok = std::randomize(v) with { v inside {[10:12]}; };\n"
             "    $display(\"%0d\", ok && v >= 10 && v <= 12);\n"
             "    bus.srandom(42);\n"
             "    other.srandom(42);\n"
             "    void'(bus.randomize());\n"
             "    void'(other.randomize());\n"
             "    $display(\"%0d\", bus.addr == other.addr);\n"
             "    randcase\n"
             "      1: taken = 1;\n"
             "      0: taken = 2;\n"
             "    endcase\n"
             "    $display(\"%0d\", taken);\n"
             "    randsequence(main)\n"
             "      main : first second;\n"
             "      first : { $write(\"first\"); };\n"
             "      second : { $display(\" second\"); };\n"
             "    endsequence\n"),
      f);
  EXPECT_EQ(out, "1\n1\n1\nfirst second\n");
}

}  // namespace
