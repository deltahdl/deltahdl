#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ConstraintDist, OnlyListedValueProduced) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {42 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 1u);
  EXPECT_EQ(RunAndGet(src, "rx"), 42u);
}

TEST(ConstraintDist, RangeElementRestrictsMembershipToRange) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[100:110] := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int inrange;\n"
      "  int outrange;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    inrange = 0;\n"
      "    outrange = 0;\n"
      "    for (int i = 0; i < 200; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x >= 100 && o.x <= 110) inrange = inrange + 1;\n"
      "      else outrange = outrange + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "inrange"), 200u);
  EXPECT_EQ(RunAndGet(src, "outrange"), 0u);
}

TEST(ConstraintDist, ZeroTotalWeightValueExcluded) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {17 := 0, 42 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int rx;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    void'(o.randomize());\n"
      "    rx = o.x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rx"), 42u);
}

TEST(ConstraintDist, ProbabilityProportionalToWeight) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {10 := 1000, 20 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int c10;\n"
      "  int c20;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    c10 = 0;\n"
      "    c20 = 0;\n"
      "    for (int i = 0; i < 200; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 10) c10 = c10 + 1;\n"
      "      if (o.x == 20) c20 = c20 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_GT(RunAndGet(src, "c10"), 150u);
  EXPECT_LT(RunAndGet(src, "c20"), 50u);
}

TEST(ConstraintDist, AbsentWeightDefaultsToOne) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {10, 20 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int c10;\n"
      "  int c20;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    c10 = 0;\n"
      "    c20 = 0;\n"
      "    for (int i = 0; i < 300; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 10) c10 = c10 + 1;\n"
      "      if (o.x == 20) c20 = c20 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_GT(RunAndGet(src, "c10"), 80u);
  EXPECT_GT(RunAndGet(src, "c20"), 80u);
}

TEST(ConstraintDist, AbsentWeightOnRangeIsPerElementDefault) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[1:4], 100}; }\n"
      "endclass\n"
      "module t;\n"
      "  int inr;\n"
      "  int at100;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    inr = 0;\n"
      "    at100 = 0;\n"
      "    for (int i = 0; i < 400; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x >= 1 && o.x <= 4) inr = inr + 1;\n"
      "      if (o.x == 100) at100 = at100 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_GT(RunAndGet(src, "inr"), RunAndGet(src, "at100") * 2);
}

TEST(ConstraintDist, WeightInterpretedAsUnsigned) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {10 := -1, 20 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int c10;\n"
      "  int c20;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    c10 = 0;\n"
      "    c20 = 0;\n"
      "    for (int i = 0; i < 200; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 10) c10 = c10 + 1;\n"
      "      if (o.x == 20) c20 = c20 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_GT(RunAndGet(src, "c10"), 195u);
  EXPECT_LT(RunAndGet(src, "c20"), 5u);
}

TEST(ConstraintDist, AssignWeightOnRangeIsPerElement) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[1:4] := 1, 100 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int inr;\n"
      "  int at100;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    inr = 0;\n"
      "    at100 = 0;\n"
      "    for (int i = 0; i < 400; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x >= 1 && o.x <= 4) inr = inr + 1;\n"
      "      if (o.x == 100) at100 = at100 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_GT(RunAndGet(src, "inr"), RunAndGet(src, "at100") * 2);
}

TEST(ConstraintDist, DivideWeightOnRangeIsWholeRange) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[1:4] :/ 1, 100 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int inr;\n"
      "  int at100;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    inr = 0;\n"
      "    at100 = 0;\n"
      "    for (int i = 0; i < 400; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x >= 1 && o.x <= 4) inr = inr + 1;\n"
      "      if (o.x == 100) at100 = at100 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  uint64_t inr = RunAndGet(src, "inr");
  uint64_t at100 = RunAndGet(src, "at100");
  EXPECT_GT(inr, at100 / 2);
  EXPECT_GT(at100, inr / 2);
}

TEST(ConstraintDist, AssignAndDivideEquivalentForSingleValues) {
  const char* assign_src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {100 := 1, 200 := 2}; }\n"
      "endclass\n"
      "module t;\n"
      "  int c100;\n"
      "  int c200;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    c100 = 0;\n"
      "    c200 = 0;\n"
      "    for (int i = 0; i < 200; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 100) c100 = c100 + 1;\n"
      "      if (o.x == 200) c200 = c200 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  const char* divide_src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {100 :/ 1, 200 :/ 2}; }\n"
      "endclass\n"
      "module t;\n"
      "  int c100;\n"
      "  int c200;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    c100 = 0;\n"
      "    c200 = 0;\n"
      "    for (int i = 0; i < 200; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 100) c100 = c100 + 1;\n"
      "      if (o.x == 200) c200 = c200 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(assign_src, "c100"), RunAndGet(divide_src, "c100"));
  EXPECT_EQ(RunAndGet(assign_src, "c200"), RunAndGet(divide_src, "c200"));
}

TEST(ConstraintDist, WeightsAreAdditiveAcrossItems) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {100 := 1, 200 := 1, 200 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int c100;\n"
      "  int c200;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    c100 = 0;\n"
      "    c200 = 0;\n"
      "    for (int i = 0; i < 300; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 100) c100 = c100 + 1;\n"
      "      if (o.x == 200) c200 = c200 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_GT(RunAndGet(src, "c200"), RunAndGet(src, "c100"));
}

TEST(ConstraintDist, ZeroWeightItemDoesNotConstrainWhenCoveredElsewhere) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {50 := 0, [50:51] := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int c50;\n"
      "  int other;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    c50 = 0;\n"
      "    other = 0;\n"
      "    for (int i = 0; i < 200; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 50) c50 = c50 + 1;\n"
      "      if (o.x != 50 && o.x != 51) other = other + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_GT(RunAndGet(src, "c50"), 0u);
  EXPECT_EQ(RunAndGet(src, "other"), 0u);
}

TEST(ConstraintDist, NonzeroWeightDoesNotExcludeValue) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {10 := 100, 20 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int c20;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    c20 = 0;\n"
      "    for (int i = 0; i < 1500; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 20) c20 = c20 + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_GT(RunAndGet(src, "c20"), 0u);
}

TEST(ConstraintDist, DefaultCoversRemainderOfDomain) {
  const char* src =
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {0 := 1, default :/ 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int czero;\n"
      "  int cother;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    czero = 0;\n"
      "    cother = 0;\n"
      "    for (int i = 0; i < 100; i = i + 1) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.x == 0) czero = czero + 1;\n"
      "      if (o.x != 0) cother = cother + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_GT(RunAndGet(src, "czero"), 0u);
  EXPECT_GT(RunAndGet(src, "cother"), 0u);
}

TEST(ConstraintDist, DistRequiresRandVariableFails) {
  const char* src =
      "class C;\n"
      "  rand int y;\n"
      "  int x;\n"
      "  constraint c { x dist {10 := 1, 20 := 1}; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    ok = o.randomize();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "ok"), 0u);
}

}  // namespace
