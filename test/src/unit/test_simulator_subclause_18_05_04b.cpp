#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string Design(const std::string& decls, const std::string& constraint,
                   int draws, const std::string& holds) {
  return "class C;\n" + decls + "  constraint c { " + constraint +
         " }\n"
         "endclass\n"
         "module t;\n"
         "  int held = 0;\n"
         "  initial begin\n"
         "    static C o = new;\n"
         "    repeat (" +
         std::to_string(draws) +
         ") begin\n"
         "      void'(o.randomize());\n"
         "      if (" +
         holds +
         ") held++;\n"
         "    end\n"
         "    $display(\"%0d\", held);\n"
         "  end\n"
         "endmodule\n";
}

TEST(UniquenessConstraintsRun, TheExcludedValueLeavesTheOtherMembers) {
  SimFixture f;
  std::string out = RunCapture(
      Design("  rand byte b;\n"
             "  rand byte c;\n"
             "  rand byte excluded;\n",
             "b inside {[4:6]}; c inside {[4:6]}; unique {b, c, excluded}; "
             "excluded == 5;",
             64, "o.excluded == 5 && o.b != 5 && o.c != 5 && o.b + o.c == 10"),
      f);
  EXPECT_EQ(out, "64\n");
}

TEST(UniquenessConstraintsRun, RealMembersNeverDrawAlike) {
  SimFixture f;
  std::string out = RunCapture(
      Design("  rand real r1;\n"
             "  rand real r2;\n",
             "r1 dist { 1.0 := 1, 2.0 := 1 }; r2 dist { 1.0 := 1, 2.0 := 1 }; "
             "unique {r1, r2};",
             64, "o.r1 != o.r2 && o.r1 + o.r2 == 3.0"),
      f);
  EXPECT_EQ(out, "64\n");
}

TEST(UniquenessConstraintsRun, AGroupOfOneMemberHasNoEffect) {
  SimFixture f;
  std::string out = RunCapture(
      Design("  rand bit [3:0] x;\n", "x == 7; unique {x};", 32, "o.x == 7"),
      f);
  EXPECT_EQ(out, "32\n");
}

TEST(UniqueConstraintRun, ASliceContributesEachElementItSelects) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [1:0] a[5];\n"
      "  rand bit [1:0] b;\n"
      "  constraint u { unique {b, a[2:3]}; }\n"
      "  constraint r { a[2] == 1; b == 1 -> a[3] == 0; }\n"
      "endclass\n"
      "module t;\n"
      "  int bad = 0;\n"
      "  initial begin\n"
      "    static C k = new;\n"
      "    repeat (30) begin\n"
      "      if (k.randomize() != 1) bad++;\n"
      "      if (k.b == k.a[2] || k.b == k.a[3] || k.a[2] == k.a[3]) bad++;\n"
      "    end\n"
      "    $display(\"%0d\", bad);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

TEST(UniqueConstraintRun, AWholeArrayAndAReversedSliceAddTheirElements) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [1:0] a[4];\n"
      "  rand bit [1:0] c[4];\n"
      "  constraint u { unique {a}; unique {c[3:2]}; c[2] == 1; }\n"
      "endclass\n"
      "module t;\n"
      "  int bad = 0;\n"
      "  bit [3:0] seen;\n"
      "  initial begin\n"
      "    static C k = new;\n"
      "    repeat (20) begin\n"
      "      if (k.randomize() != 1) bad++;\n"
      "      seen = 0;\n"
      "      foreach (k.a[i]) seen[k.a[i]] = 1;\n"
      "      if (seen != 4'hF || k.c[3] == 1) bad++;\n"
      "    end\n"
      "    $display(\"%0d\", bad);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

}  // namespace
