#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// The classes of test/src/e2e/external_constraint_blocks.sv around the
// statements of an initial that holds a C c and an E e, with the module's
// counters.
std::string Design(const std::string& body) {
  return "class C;\n"
         "  rand int x;\n"
         "  constraint proto1;\n"
         "  extern constraint proto2;\n"
         "endclass\n"
         "constraint C::proto1 { x inside {-4, 5, 7}; }\n"
         "constraint C::proto2 { x >= 0; }\n"
         "class E;\n"
         "  rand bit [7:0] y;\n"
         "  constraint empty;\n"
         "endclass\n"
         "module t;\n"
         "  int both = 0, at_least_zero = 0, freed = 0, solved = 0;\n"
         "  bit [255:0] seen = 0;\n"
         "  int distinct = 0;\n"
         "  initial begin\n"
         "    static C c = new;\n"
         "    static E e = new;\n" +
         body +
         "  end\n"
         "endmodule\n";
}

// 18.5.1: a prototype of either form is completed by the external block
// named through the class scope, so both blocks hold and x is 5 or 7.
TEST(ExternalConstraintBlocksRun, BothFormsOfPrototypeAreCompleted) {
  const std::string kSrc = Design(
      "    repeat (32) begin\n"
      "      void'(c.randomize());\n"
      "      if (c.x == 5 || c.x == 7) both++;\n"
      "    end\n"
      "    $finish;\n");
  EXPECT_EQ(RunAndGet(kSrc, "both"), uint64_t{32});
}

// 18.5.1: the completed block keeps its prototype's name, which names it to
// constraint_mode(), so with proto1 off only proto2 holds x to at least 0.
TEST(ExternalConstraintBlocksRun, TheCompletedBlockKeepsThePrototypesName) {
  const std::string kSrc = Design(
      "    c.proto1.constraint_mode(0);\n"
      "    repeat (32) begin\n"
      "      void'(c.randomize());\n"
      "      if (c.x >= 0) at_least_zero++;\n"
      "      if (c.x != 5 && c.x != 7) freed++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", at_least_zero, freed > 0);\n"
      "    $finish;\n");
  SimFixture f;
  EXPECT_EQ(RunCapture(kSrc, f), "32 1\n$finish at time 0\n");
}

// 18.5.1: an implicit prototype with no external block is an empty
// constraint, which has no effect: randomize() succeeds and y is free.
TEST(ExternalConstraintBlocksRun, AnUncompletedImplicitPrototypeIsEmpty) {
  const std::string kSrc = Design(
      "    repeat (64) begin\n"
      "      if (e.randomize()) solved++;\n"
      "      seen[e.y] = 1;\n"
      "    end\n"
      "    for (int i = 0; i < 256; i++) if (seen[i]) distinct++;\n"
      "    $display(\"%0d %0d\", solved, distinct > 1);\n"
      "    $finish;\n");
  SimFixture f;
  EXPECT_EQ(RunCapture(kSrc, f), "64 1\n$finish at time 0\n");
}

// 18.5.1 with 26.2: an external block declared in a package completes the
// prototype of the package's class, as a block at compilation-unit scope does
// the compilation unit's. The compilation unit declares a C of its own, whose
// prototype the package's block, naming C in another scope, leaves empty, so
// its x stays free while the package's x lands in 70..75.
TEST(ExternalConstraintBlocksRun, ABlockInAPackageCompletesThePackagesClass) {
  const char* src =
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "  constraint proto1;\n"
      "endclass\n"
      "package pkg;\n"
      "  class C;\n"
      "    rand int x;\n"
      "    constraint proto1;\n"
      "  endclass\n"
      "  constraint C::proto1 { x inside {[70:75]}; }\n"
      "endpackage\n"
      "module t;\n"
      "  int in_range = 0, outside = 0;\n"
      "  initial begin\n"
      "    static pkg::C p = new;\n"
      "    static C c = new;\n"
      "    repeat (32) begin\n"
      "      if (p.randomize() && p.x inside {[70:75]}) in_range++;\n"
      "      void'(c.randomize());\n"
      "      if (!(c.x inside {[70:75]})) outside++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", in_range, outside > 0);\n"
      "  end\n"
      "endmodule\n";
  SimFixture f;
  EXPECT_EQ(RunCapture(src, f), "32 1\n");
}

}  // namespace
