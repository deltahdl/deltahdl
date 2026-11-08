#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

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

TEST(ExternalConstraintBlocksRun, BothFormsOfPrototypeAreCompleted) {
  const std::string kSrc = Design(
      "    repeat (32) begin\n"
      "      void'(c.randomize());\n"
      "      if (c.x == 5 || c.x == 7) both++;\n"
      "    end\n"
      "    $finish;\n");
  EXPECT_EQ(RunAndGet(kSrc, "both"), uint64_t{32});
}

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

TEST(ExternalConstraintBlocksRun, ABlockInAModuleCompletesTheModulesClass) {
  const char* src =
      "module t;\n"
      "  class C;\n"
      "    rand bit [3:0] x;\n"
      "    extern constraint p;\n"
      "  endclass\n"
      "  constraint C::p { x == 5; }\n"
      "  int fives = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (16) if (c.randomize() && c.x == 5) fives++;\n"
      "    $display(\"%0d\", fives);\n"
      "  end\n"
      "endmodule\n";
  SimFixture f;
  EXPECT_EQ(RunCapture(src, f), "16\n");
}

TEST(ExternalConstraintBlocksRun, ABlockInAGenerateBlockCompletesItsClass) {
  const char* src =
      "module t;\n"
      "  if (1) begin : g\n"
      "    class C;\n"
      "      rand bit [3:0] x;\n"
      "      constraint p;\n"
      "    endclass\n"
      "    constraint C::p { x == 9; }\n"
      "    int nines = 0;\n"
      "    initial begin\n"
      "      static C c = new;\n"
      "      repeat (16) if (c.randomize() && c.x == 9) nines++;\n"
      "      $display(\"%0d\", nines);\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  SimFixture f;
  EXPECT_EQ(RunCapture(src, f), "16\n");
}

TEST(ExternalConstraintBlocksRun, ABlockInAProgramCompletesItsClass) {
  const char* src =
      "program t;\n"
      "  class C;\n"
      "    rand bit [3:0] x;\n"
      "    constraint p;\n"
      "  endclass\n"
      "  constraint C::p { x == 12; }\n"
      "  int twelves = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (16) if (c.randomize() && c.x == 12) twelves++;\n"
      "    $display(\"%0d\", twelves);\n"
      "  end\n"
      "endprogram\n";
  SimFixture f;
  EXPECT_EQ(RunCapture(src, f), "16\n");
}

std::string Completed(const std::string& members, const std::string& block,
                      const std::string& bad_when) {
  return "class C;\n" + members + "  constraint p;\nendclass\n" +
         "constraint C::p { " + block + " }\n" +
         "module t;\n"
         "  int bad = 0;\n"
         "  initial begin\n"
         "    static C c = new;\n"
         "    repeat (40) begin\n"
         "      void'(c.randomize());\n"
         "      if (" +
         bad_when +
         ") bad++;\n"
         "    end\n"
         "    $display(\"bad %0d\", bad);\n"
         "  end\n"
         "endmodule\n";
}

TEST(ExternalConstraintBlocksRun, ADistributionInTheBlockHolds) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                Completed("  rand bit [3:0] x;\n", "x dist { 3 := 1, 9 := 1 };",
                          "c.x != 3 && c.x != 9"),
                f),
            "bad 0\n");
}

TEST(ExternalConstraintBlocksRun, AUniqueGroupInTheBlockHolds) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Completed("  rand bit [1:0] a, b;\n", "unique {a, b};",
                                 "c.a == c.b"),
                       f),
            "bad 0\n");
}

TEST(ExternalConstraintBlocksRun, AForeachInTheBlockHolds) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Completed("  rand bit [3:0] a[4];\n",
                                 "foreach (a[i]) a[i] == i;",
                                 "c.a[0] != 0 || c.a[1] != 1 || c.a[2] != 2 || "
                                 "c.a[3] != 3"),
                       f),
            "bad 0\n");
}

TEST(ExternalConstraintBlocksRun, ASoftDistributionInTheBlockHolds) {
  SimFixture f;
  EXPECT_EQ(RunCapture(Completed("  rand bit [3:0] x;\n",
                                 "soft x dist { 3 := 1, 9 := 1 };",
                                 "c.x != 3 && c.x != 9"),
                       f),
            "bad 0\n");
}

int BadCount(const std::string& src) {
  SimFixture f;
  return std::stoi(RunCapture(src, f).substr(4));
}

TEST(ExternalConstraintBlocksRun, ADisableSoftInTheBlockHolds) {
  EXPECT_LT(BadCount(Completed("  rand bit [3:0] x;\n"
                               "  constraint q { soft x == 3; }\n",
                               "disable soft x;", "c.x == 3")),
            20);
}

TEST(ExternalConstraintBlocksRun, ASolveBeforeInTheBlockHolds) {
  EXPECT_GT(BadCount(Completed("  rand bit s;\n  rand bit [7:0] d;\n"
                               "  constraint q { s -> d == 0; }\n",
                               "solve s before d;", "c.s")),
            5);
}

}  // namespace
