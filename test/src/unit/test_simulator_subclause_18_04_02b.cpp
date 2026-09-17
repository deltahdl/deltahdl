#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// The classes of test/src/e2e/randc_modifier.sv around the statements of an
// initial that holds a Cyclic cy, a Wide w, a Changing ch and the Shared s1
// and s2, with the module's seen, visited, groups, distinct and confined.
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
         "    Cyclic cy = new;\n"
         "    Wide w = new;\n"
         "    Changing ch = new;\n"
         "    Shared s1 = new;\n"
         "    Shared s2 = new;\n" +
         body +
         "  end\n"
         "endmodule\n";
}

// §18.4.2: a randc variable returns the values of a random permutation of
// its range in order on successive calls and computes a new permutation
// after the last, so each of three iterations of the 2-bit y visits all
// four values, and the 8-bit z, the least an implementation may cap a
// randc at, visits all 256 values in 256 calls.
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

// §18.4.2: the permutation is recomputed whenever the constraints on the
// variable change: with hi off an iteration of c visits all four values,
// and with hi on the next four calls hold c to 2 and 3, both seen.
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

// §18.4.2: a static randc variable keeps its cyclic state with the class,
// so randomize() through either of two instances takes the next value of
// the one sequence and four calls across them visit all four values.
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

}  // namespace
