#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string Counting(const std::string& decls, int draws,
                     const std::string& holds, const std::string& after) {
  return "class C;\n" + decls +
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
         "    $display(\"%0d %0d\", held, " +
         after +
         ");\n"
         "  end\n"
         "endmodule\n";
}

TEST(ForeachIterativeConstraintsRun, ASizeConstraintSizesTheArray) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand int A[];\n"
      "  constraint c1 { A.size inside {[1:10]}; }\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0, smallest = 11, largest = 0;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    repeat (64) begin\n"
      "      void'(o.randomize());\n"
      "      if (o.A.size() >= 1 && o.A.size() <= 10) held++;\n"
      "      if (o.A.size() < smallest) smallest = o.A.size();\n"
      "      if (o.A.size() > largest) largest = o.A.size();\n"
      "    end\n"
      "    $display(\"%0d %0d\", held, largest > smallest);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "64 1\n");
}

TEST(ForeachIterativeConstraintsRun, APredicateGuardsTheConstraint) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand int A[];\n"
      "  constraint c1 { A.size inside {[1:10]}; }\n"
      "  constraint c2 { foreach (A[k]) (k < A.size - 1) -> A[k + 1] > A[k]; "
      "}\n"
      "endclass\n"
      "module t;\n"
      "  int held = 0, ok = 0, longest = 0;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    repeat (64) begin\n"
      "      void'(o.randomize());\n"
      "      ok = 1;\n"
      "      for (int i = 1; i < o.A.size(); i++)\n"
      "        if (o.A[i] <= o.A[i - 1]) ok = 0;\n"
      "      if (ok) held++;\n"
      "      if (o.A.size() > longest) longest = o.A.size();\n"
      "    end\n"
      "    $display(\"%0d %0d\", held, longest > 4);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "64 1\n");
}

TEST(ForeachIterativeConstraintsRun, AGuardedRelationBetweenElementsHolds) {
  SimFixture f;
  std::string out = RunCapture(
      Counting(
          "  rand int A[8];\n"
          "  constraint c { foreach (A[i]) (i > 0) -> A[i] > A[i - 1]; }\n",
          32,
          "o.A[1] > o.A[0] && o.A[2] > o.A[1] && o.A[3] > o.A[2] && "
          "o.A[4] > o.A[3] && o.A[5] > o.A[4] && o.A[6] > o.A[5] && "
          "o.A[7] > o.A[6]",
          "o.A[7] > o.A[0]"),
      f);
  EXPECT_EQ(out, "32 1\n");
}

TEST(ForeachIterativeConstraintsRun, AGuardedEqualityBetweenElementsHolds) {
  SimFixture f;
  std::string out = RunCapture(
      Counting("  rand int A[6];\n"
               "  constraint c { foreach (A[i]) (i > 0) -> A[i] == A[i - 1] + "
               "1; }\n",
               32, "o.A[5] == o.A[0] + 5 && o.A[3] == o.A[2] + 1",
               "o.A[1] == o.A[0] + 1"),
      f);
  EXPECT_EQ(out, "32 1\n");
}

TEST(ForeachIterativeConstraintsRun, AGuardOverTheSizeHoldsAtAFixedSize) {
  SimFixture f;
  std::string out = RunCapture(
      Counting("  rand int A[];\n"
               "  constraint c1 { A.size == 8; }\n"
               "  constraint c2 { foreach (A[k]) (k < A.size - 1) -> A[k + 1] "
               "> A[k]; }\n",
               16,
               "o.A[1] > o.A[0] && o.A[2] > o.A[1] && o.A[3] > o.A[2] && "
               "o.A[4] > o.A[3] && o.A[5] > o.A[4] && o.A[6] > o.A[5] && "
               "o.A[7] > o.A[6]",
               "o.A.size()"),
      f);
  EXPECT_EQ(out, "16 8\n");
}

TEST(ForeachIterativeConstraintsRun, AGuardOverTheIndexHoldsAtADrawnSize) {
  SimFixture f;
  std::string out = RunCapture(
      Counting("  rand int A[];\n"
               "  constraint c1 { A.size inside {[8:8]}; }\n"
               "  constraint c2 { foreach (A[k]) (k < 7) -> A[k + 1] > A[k]; "
               "}\n",
               16,
               "o.A[1] > o.A[0] && o.A[2] > o.A[1] && o.A[3] > o.A[2] && "
               "o.A[4] > o.A[3] && o.A[5] > o.A[4] && o.A[6] > o.A[5] && "
               "o.A[7] > o.A[6]",
               "o.A.size()"),
      f);
  EXPECT_EQ(out, "16 8\n");
}

TEST(ForeachIterativeConstraintsRun, AGuardOverTheSizeHoldsAnEquality) {
  SimFixture f;
  std::string out = RunCapture(
      Counting("  rand int A[];\n"
               "  constraint c1 { A.size == 8; }\n"
               "  constraint c2 { foreach (A[k]) (k < A.size - 1) -> A[k + 1] "
               "== A[k] + 1; }\n",
               16, "o.A[7] == o.A[0] + 7 && o.A[4] == o.A[3] + 1",
               "o.A.size()"),
      f);
  EXPECT_EQ(out, "16 8\n");
}

TEST(ForeachIterativeConstraintsRun, TheSizeIsAStateVariableInTheForeach) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand int A[];\n"
      "  constraint c1 { A.size == 3; }\n"
      "  constraint c2 { foreach (A[i]) A[i] == A.size + i; }\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    void'(o.randomize());\n"
      "    $display(\"%0d %0d %0d %0d\", o.A.size(), o.A[0], o.A[1], o.A[2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 3 4 5\n");
}

TEST(ForeachIterativeConstraintsRun, AnUnconstrainedSizeIsKept) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand int A[];\n"
      "  constraint each { foreach (A[i]) A[i] == i * 3; }\n"
      "  function void resize(int n);\n"
      "    A = new[n];\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    o.resize(5);\n"
      "    void'(o.randomize());\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", o.A.size(), o.A[0], o.A[1],\n"
      "             o.A[2], o.A[3], o.A[4]);\n"
      "    o.A = new[2];\n"
      "    void'(o.randomize());\n"
      "    $display(\"%0d %0d %0d\", o.A.size(), o.A[0], o.A[1]);\n"
      "    o.A.delete();\n"
      "    $display(\"%0d\", o.A.size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5 0 3 6 9 12\n2 0 3\n0\n");
}

TEST(ForeachIterativeConstraintsRun, AnIndexExpressionMayHoldAStateVariable) {
  SimFixture f;
  std::string out = RunCapture(
      Counting("  rand int B[4];\n"
               "  int off = 2;\n"
               "  constraint range { foreach (B[i]) B[i] inside {[0:99]}; }\n"
               "  constraint step { foreach (B[i]) (i >= off) -> B[i] == B[i - "
               "off] + 1; }\n",
               32, "o.B[2] == o.B[0] + 1 && o.B[3] == o.B[1] + 1",
               "o.B[0] < 100"),
      f);
  EXPECT_EQ(out, "32 1\n");
}

TEST(ForeachIterativeConstraintsRun, TheLoopVariableShadowsAProperty) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [3:0] A[3];\n"
      "  int k = 100;\n"
      "  constraint c { foreach (A[k]) A[k] == k + 1; }\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    static C o = new;\n"
      "    void'(o.randomize());\n"
      "    $display(\"%0d %0d %0d %0d\", o.A[0], o.A[1], o.A[2], o.k);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2 3 100\n");
}

TEST(ForeachConstraintRun, TwoLoopVariablesIterateBothDimensions) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [7:0] m[2][3];\n"
      "  constraint c { foreach (m[i, j]) m[i][j] == 10 * i + j + 1; }\n"
      "endclass\n"
      "module t;\n"
      "  int ok, bad = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    ok = c.randomize();\n"
      "    for (int i = 0; i < 2; i++)\n"
      "      for (int j = 0; j < 3; j++)\n"
      "        if (c.m[i][j] != 10 * i + j + 1) bad++;\n"
      "    $display(\"%0d %0d %0d\", ok, bad, c.m[1][2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 0 13\n");
}

TEST(ForeachConstraintRun, AForeachIteratesTheCharactersOfAString) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  string s = \"AB\";\n"
      "  rand byte b;\n"
      "  constraint c { foreach (s[i]) b != s[i] && b != s[i + 1];\n"
      "                 b inside {65, 66, 67}; }\n"
      "endclass\n"
      "class D;\n"
      "  rand byte b;\n"
      "  constraint c { b inside {65, 66}; }\n"
      "endclass\n"
      "module t;\n"
      "  string u = \"A\";\n"
      "  int cs = 0, ds = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    static D d = new;\n"
      "    repeat (10) begin\n"
      "      void'(c.randomize());\n"
      "      if (c.b == 67) cs++;\n"
      "      void'(d.randomize() with { foreach (u[j]) b != u[j]; });\n"
      "      if (d.b == 66) ds++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", cs, ds);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "10 10\n");
}

}  // namespace
