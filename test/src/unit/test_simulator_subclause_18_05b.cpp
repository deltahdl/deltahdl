#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// The classes of test/src/e2e/constraint_blocks.sv around the statements of
// an initial that holds an Item it and an Other ot, with the module's
// counters.
std::string Design(const std::string& body) {
  return "class Item;\n"
         "  rand bit [7:0] lo;\n"
         "  rand bit [7:0] hi;\n"
         "  bit [7:0] limit = 100;\n"
         "  constraint range { lo >= 10; lo <= 20; }\n"
         "  constraint order { hi > lo; hi < limit; }\n"
         "  constraint spacing { (hi - lo) % 4 == 0; }\n"
         "endclass\n"
         "class Other;\n"
         "  rand bit [3:0] n;\n"
         "  constraint range { n inside {[4:6]}; }\n"
         "endclass\n"
         "module t;\n"
         "  int in_range = 0, ordered = 0, spaced = 0, under_limit = 0;\n"
         "  int escaped = 0, still_ordered = 0, other_in_range = 0;\n"
         "  initial begin\n"
         "    Item it = new;\n"
         "    Other ot = new;\n" +
         body +
         "  end\n"
         "endmodule\n";
}

// 18.5: the constraint blocks of a class all determine the values of its
// random variables, each statement of each block holding at once: lo's two
// range statements, hi's relations to lo and to the state variable limit,
// and the arithmetic expression on their difference.
TEST(ConstraintBlocksRun, EveryStatementOfEveryBlockHoldsAtOnce) {
  const std::string kSrc = Design(
      "    repeat (64) begin\n"
      "      void'(it.randomize());\n"
      "      if (it.lo >= 10 && it.lo <= 20) in_range++;\n"
      "      if (it.hi > it.lo && it.hi < 100) ordered++;\n"
      "      if ((it.hi - it.lo) % 4 == 0) spaced++;\n"
      "    end\n"
      "    $display(\"%0d %0d %0d\", in_range, ordered, spaced);\n"
      "    $finish;\n");
  SimFixture f;
  EXPECT_EQ(RunCapture(kSrc, f), "64 64 64\n$finish at time 0\n");
}

// 18.5: a relation against a state variable reads the variable's value
// current at the call, so lowering limit bounds hi below it.
TEST(ConstraintBlocksRun, AStateVariablesCurrentValueBoundsTheDraw) {
  const std::string kSrc = Design(
      "    it.limit = 30;\n"
      "    repeat (64) begin\n"
      "      void'(it.randomize());\n"
      "      if (it.hi > it.lo && it.hi < 30) under_limit++;\n"
      "    end\n"
      "    $finish;\n");
  EXPECT_EQ(RunAndGet(kSrc, "under_limit"), uint64_t{64});
}

// 18.5: the block's name names it to constraint_mode(), so turning range
// off frees lo from 10 to 20 while the other blocks still hold.
TEST(ConstraintBlocksRun, ABlockTurnedOffByNameLeavesTheOthersHolding) {
  const std::string kSrc = Design(
      "    it.range.constraint_mode(0);\n"
      "    repeat (64) begin\n"
      "      void'(it.randomize());\n"
      "      if (it.lo < 10 || it.lo > 20) escaped++;\n"
      "      if (it.hi > it.lo && it.hi < 100 && (it.hi - it.lo) % 4 == 0)\n"
      "        still_ordered++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", escaped > 0, still_ordered);\n"
      "    $finish;\n");
  SimFixture f;
  EXPECT_EQ(RunCapture(kSrc, f), "1 64\n$finish at time 0\n");
}

// 18.5: a block's name is unique within its class, not across classes, so
// Other's own block named range constrains its n.
TEST(ConstraintBlocksRun, ABlockNameIsUniqueWithinItsClassAlone) {
  const std::string kSrc = Design(
      "    repeat (16) begin\n"
      "      void'(ot.randomize());\n"
      "      if (ot.n >= 4 && ot.n <= 6) other_in_range++;\n"
      "    end\n"
      "    $finish;\n");
  EXPECT_EQ(RunAndGet(kSrc, "other_in_range"), uint64_t{16});
}

}  // namespace
