#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// The Packet of test/src/e2e/constraint_driven_generation.sv, an object
// modelling the data to be randomized with random variables and the
// constraints that determine their legal values, around the statements of
// an initial.
std::string Design(const std::string& body) {
  return "typedef enum {RUNT, PLAIN, JUMBO} kind_t;\n"
         "class Packet;\n"
         "  rand kind_t kind;\n"
         "  rand int length;\n"
         "  rand bit tag;\n"
         "  constraint legal {\n"
         "    kind == RUNT -> length inside {[1:63]};\n"
         "    kind == PLAIN -> length inside {[64:1518]};\n"
         "    kind == JUMBO -> length == 9000;\n"
         "    tag -> kind == PLAIN;\n"
         "  }\n"
         "  function bit meets_constraints();\n"
         "    case (kind)\n"
         "      RUNT: meets_constraints = length >= 1 && length <= 63 && "
         "!tag;\n"
         "      PLAIN: meets_constraints = length >= 64 && length <= 1518;\n"
         "      JUMBO: meets_constraints = length == 9000 && !tag;\n"
         "    endcase\n"
         "  endfunction\n"
         "endclass\n"
         "module t;\n"
         "  initial begin\n"
         "    Packet p = new;\n"
         "    int legal = 0, solved = 0;\n" +
         body +
         "  end\n"
         "endmodule\n";
}

// §18.2: the constraints, written declaratively on the object, are
// processed by a solver that generates random values meeting them, so
// every randomize() of the Packet succeeds and yields values its own
// check finds legal.
TEST(ConstraintDrivenGeneration, EveryRandomizeMeetsTheConstraints) {
  SimFixture f;
  std::string out =
      RunCapture(Design("    repeat (24) begin\n"
                        "      if (p.randomize()) solved++;\n"
                        "      if (p.meets_constraints()) legal++;\n"
                        "    end\n"
                        "    $display(\"%0d %0d\", solved, legal);\n"),
                 f);
  EXPECT_EQ(out, "24 24\n");
}

// §18.2: a corner case the constraints reach without a directed test
// naming it: a jumbo is 9000 long and, tag implying a plain frame,
// untagged.
TEST(ConstraintDrivenGeneration, TheConstraintsReachACorner) {
  SimFixture f;
  std::string out =
      RunCapture(Design("    void'(p.randomize() with { kind == JUMBO; });\n"
                        "    $display(\"%0d %0d\", p.length, p.tag);\n"),
                 f);
  EXPECT_EQ(out, "9000 0\n");
}

}  // namespace
