#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A Packet holding its size below 64, and the derived classes the cases
// randomize, one adding a constraint over the size and one contradicting
// the base's.
const char* const kPackets =
    "class Packet;\n"
    "  rand bit [7:0] kind;\n"
    "  rand bit [7:0] size;\n"
    "  constraint small { size < 64; }\n"
    "endclass\n"
    "class Framed extends Packet;\n"
    "  constraint even { size[0] == 0; }\n"
    "endclass\n"
    "class Oversized extends Packet;\n"
    "  constraint large { size > 100; }\n"
    "endclass\n";

// 18.6.1: randomize() is a virtual method, so called through a Packet
// handle to a Framed it applies the constraints of the object's own class:
// over 32 draws every call returns 1 with the size below 64 and even, as
// the design test/src/e2e/randomize_method.sv runs it.
TEST(RandomizeMethodRun, TheVirtualMethodRandomizesTheObjectsOwnClass) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(kPackets) +
                     "module t;\n"
                     "  int success = 0, held = 0, evens = 0;\n"
                     "  initial begin\n"
                     "    Framed fr = new;\n"
                     "    Packet handle = fr;\n"
                     "    repeat (32) begin\n"
                     "      if (handle.randomize()) success++;\n"
                     "      if (fr.size < 64) held++;\n"
                     "      if (fr.size[0] == 0) evens++;\n"
                     "    end\n"
                     "    $display(\"%0d %0d %0d\", success, held, evens);\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_EQ(out, "32 32 32\n");
}

// 18.6.1: the addition of constraints in a derived class can render a
// seemingly simple constraint unsatisfiable: the Oversized holds its size
// above 100 beside the base's below 64, so randomize() returns 0 and the
// size keeps the value it had rather than the bound the empty range was
// collapsed onto.
TEST(RandomizeMethodRun, ADerivedClassCanRenderTheConstraintsUnsatisfiable) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(kPackets) +
                     "module t;\n"
                     "  int success;\n"
                     "  initial begin\n"
                     "    Oversized ov = new;\n"
                     "    ov.size = 5;\n"
                     "    success = ov.randomize();\n"
                     "    $display(\"%0d %0d\", success, ov.size);\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_EQ(out, "0 5\n");
}

}  // namespace
