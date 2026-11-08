#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string Design(const std::string& body) {
  return "class Cyclic;\n"
         "  randc bit [1:0] y;\n"
         "endclass\n"
         "class Wide;\n"
         "  randc bit [7:0] z;\n"
         "endclass\n"
         "class Changing;\n"
         "  randc bit [1:0] c;\n"
         "  constraint hi { c >= 2; }\n"
         "endclass\n"
         "class Shared;\n"
         "  static randc bit [1:0] s;\n"
         "endclass\n"
         "module t;\n"
         "  bit [3:0] seen;\n"
         "  bit [255:0] visited;\n"
         "  int groups = 0, distinct = 0, confined = 0;\n"
         "  initial begin\n"
         "    static Cyclic cy = new;\n"
         "    static Wide w = new;\n"
         "    static Changing ch = new;\n"
         "    static Shared s1 = new;\n"
         "    static Shared s2 = new;\n" +
         body +
         "  end\n"
         "endmodule\n";
}

TEST(RandcModifierRun, EachIterationVisitsEveryValueOnce) {
  SimFixture f;
  std::string out = RunCapture(
      Design("    repeat (3) begin\n"
             "      seen = 0;\n"
             "      repeat (4) begin\n"
             "        void'(cy.randomize());\n"
             "        seen[cy.y] = 1;\n"
             "      end\n"
             "      if (seen == 4'b1111) groups++;\n"
             "    end\n"
             "    repeat (256) begin\n"
             "      void'(w.randomize());\n"
             "      visited[w.z] = 1;\n"
             "    end\n"
             "    for (int k = 0; k < 256; k++) if (visited[k]) distinct++;\n"
             "    $display(\"%0d %0d\", groups, distinct);\n"),
      f);
  EXPECT_EQ(out, "3 256\n");
}

TEST(RandcModifierRun, ThePermutationIsRecomputedWhenConstraintsChange) {
  SimFixture f;
  std::string out = RunCapture(
      Design("    ch.hi.constraint_mode(0);\n"
             "    seen = 0;\n"
             "    repeat (4) begin\n"
             "      void'(ch.randomize());\n"
             "      seen[ch.c] = 1;\n"
             "    end\n"
             "    $display(\"%0d\", seen == 4'b1111);\n"
             "    ch.hi.constraint_mode(1);\n"
             "    seen = 0;\n"
             "    repeat (4) begin\n"
             "      void'(ch.randomize());\n"
             "      seen[ch.c] = 1;\n"
             "      if (ch.c >= 2) confined++;\n"
             "    end\n"
             "    $display(\"%0d %0d\", confined, seen == 4'b1100);\n"),
      f);
  EXPECT_EQ(out, "1\n4 1\n");
}

TEST(RandcModifierRun, AStaticRandcSharesOneSequenceAcrossInstances) {
  SimFixture f;
  std::string out =
      RunCapture(Design("    seen = 0;\n"
                        "    void'(s1.randomize()); seen[s1.s] = 1;\n"
                        "    void'(s2.randomize()); seen[s2.s] = 1;\n"
                        "    void'(s1.randomize()); seen[s1.s] = 1;\n"
                        "    void'(s2.randomize()); seen[s2.s] = 1;\n"
                        "    $display(\"%0d\", seen == 4'b1111);\n"),
                 f);
  EXPECT_EQ(out, "1\n");
}

TEST(RandcCycleRun, AConstrainedDomainIsCycledWithoutRepeats) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  randc bit [3:0] y;\n"
      "  constraint r { y inside {[10:15]}; }\n"
      "endclass\n"
      "module t;\n"
      "  int bad = 0;\n"
      "  bit [15:0] seen;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (2) begin\n"
      "      seen = 0;\n"
      "      repeat (6) begin\n"
      "        if (c.randomize() != 1 || c.y < 10 || seen[c.y]) bad++;\n"
      "        seen[c.y] = 1;\n"
      "      end\n"
      "      if (seen != 16'hFC00) bad++;\n"
      "    end\n"
      "    $display(\"%0d\", bad);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

TEST(RandcCycleRun, AChangedConstraintRecomputesThePermutation) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  randc bit [2:0] y;\n"
      "  int lo = 0;\n"
      "  constraint c { y >= lo; }\n"
      "endclass\n"
      "module t;\n"
      "  int bad = 0;\n"
      "  bit [7:0] seen = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (2) void'(c.randomize());\n"
      "    c.lo = 5;\n"
      "    repeat (3) begin\n"
      "      if (c.randomize() != 1 || c.y < 5 || seen[c.y]) bad++;\n"
      "      seen[c.y] = 1;\n"
      "    end\n"
      "    $display(\"%0d %0d\", bad, seen);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 224\n");
}

TEST(RandcCycleRun, AConstraintTurnedOffRestartsThePermutation) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  randc bit [1:0] y;\n"
      "  constraint c { y inside {[0:1]}; }\n"
      "endclass\n"
      "module t;\n"
      "  int bad = 0;\n"
      "  bit [3:0] seen = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (2) void'(c.randomize());\n"
      "    c.c.constraint_mode(0);\n"
      "    repeat (4) begin\n"
      "      if (c.randomize() != 1 || seen[c.y]) bad++;\n"
      "      seen[c.y] = 1;\n"
      "    end\n"
      "    $display(\"%0d %0d\", bad, seen);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 15\n");
}

}  // namespace
