#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(VariableOrdering, UniformOverLegalCombinationsWithoutOrdering) {
  const char* src =
      "class B;\n"
      "  rand bit s;\n"
      "  rand bit [1:0] d;\n"
      "  constraint c { s -> d == 0; }\n"
      "endclass\n"
      "module t;\n"
      "  int ones;\n"
      "  initial begin\n"
      "    static B o = new;\n"
      "    ones = 0;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.s == 1) ones = ones + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  auto ones = RunAndGet(src, "ones");
  EXPECT_GE(ones, 50u);
  EXPECT_LE(ones, 210u);
}

TEST(VariableOrdering, SolveBeforeShiftsDistributionTowardOrderedVariable) {
  const char* src =
      "class B;\n"
      "  rand bit s;\n"
      "  rand bit [1:0] d;\n"
      "  constraint c { s -> d == 0; }\n"
      "  constraint ord { solve s before d; }\n"
      "endclass\n"
      "module t;\n"
      "  int ones;\n"
      "  initial begin\n"
      "    static B o = new;\n"
      "    ones = 0;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.s == 1) ones = ones + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  auto ones = RunAndGet(src, "ones");
  EXPECT_GE(ones, 240u);
  EXPECT_LE(ones, 360u);
}

TEST(VariableOrdering, OrderingPreservesSolutionSpace) {
  const char* src =
      "class B;\n"
      "  rand bit s;\n"
      "  rand bit [1:0] d;\n"
      "  constraint c { s -> d == 0; }\n"
      "  constraint ord { solve s before d; }\n"
      "endclass\n"
      "module t;\n"
      "  int good;\n"
      "  initial begin\n"
      "    static B o = new;\n"
      "    static int saw0 = 0; static int saw1 = 0; static int bad = 0;\n"
      "    for (int i = 0; i < 400; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.s == 1) begin\n"
      "        saw1 = 1;\n"
      "        if (o.d != 0) bad = 1;\n"
      "      end else saw0 = 1;\n"
      "    end\n"
      "    good = (saw0 && saw1 && !bad) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "good"), 1u);
}

TEST(VariableOrdering, OrderingNeverCausesFailure) {
  const char* src =
      "class B;\n"
      "  rand bit s;\n"
      "  rand bit [1:0] d;\n"
      "  constraint c { s -> d == 0; }\n"
      "  constraint ord { solve s before d; }\n"
      "endclass\n"
      "module t;\n"
      "  int allok;\n"
      "  initial begin\n"
      "    static B o = new;\n"
      "    allok = 1;\n"
      "    for (int i = 0; i < 400; i = i + 1) begin\n"
      "      if (o.randomize() == 0) allok = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "allok"), 1u);
}

TEST(VariableOrdering, UnorderedVariableSolvedWithLastSet) {
  const char* src =
      "class B;\n"
      "  rand bit a;\n"
      "  rand bit d;\n"
      "  rand bit u;\n"
      "  constraint c { u -> a == 0; }\n"
      "  constraint ord { solve a before d; }\n"
      "endclass\n"
      "module t;\n"
      "  int aones; int uones;\n"
      "  initial begin\n"
      "    static B o = new;\n"
      "    aones = 0; uones = 0;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.a == 1) aones = aones + 1;\n"
      "      if (o.u == 1) uones = uones + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  auto aones = RunAndGet(src, "aones");
  EXPECT_GE(aones, 240u);
  EXPECT_LE(aones, 360u);
  auto uones = RunAndGet(src, "uones");
  EXPECT_GE(uones, 90u);
  EXPECT_LE(uones, 195u);
}

TEST(VariableOrdering, PartiallyOrderedVariablesSolvedWithLatestSet) {
  const char* src =
      "class B;\n"
      "  rand bit a;\n"
      "  rand bit b;\n"
      "  rand bit [1:0] c;\n"
      "  constraint dep { a -> c == 0; b -> c == 0; }\n"
      "  constraint ord { solve a before c; solve b before c; }\n"
      "endclass\n"
      "module t;\n"
      "  int aones; int ok;\n"
      "  initial begin\n"
      "    static B o = new;\n"
      "    aones = 0; ok = 1;\n"
      "    for (int i = 0; i < 600; i = i + 1) begin\n"
      "      if (o.randomize() == 0) ok = 0;\n"
      "      if (o.a == 1) aones = aones + 1;\n"
      "      if ((o.a || o.b) && o.c != 0) ok = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  auto aones = RunAndGet(src, "aones");
  EXPECT_GE(aones, 240u);
  EXPECT_LE(aones, 360u);
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
}

}  // namespace
