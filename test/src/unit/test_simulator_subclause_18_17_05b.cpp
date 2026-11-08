#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string Grammar(const std::string& head) {
  return "      randsequence( TOP )\n"
         "        TOP : " +
         head +
         " S1 S2 ;\n"
         "        S1  : A B ;\n"
         "        S2  : C D ;\n"
         "        A   : { seq[p] = 1; p++; } ;\n"
         "        B   : { seq[p] = 2; p++; } ;\n"
         "        C   : { seq[p] = 3; p++; } ;\n"
         "        D   : { seq[p] = 4; p++; } ;\n"
         "      endsequence\n";
}

const char* const kHead =
    "module t;\n"
    "  int i, p, code, seq[4], counts[6], codes[6];\n"
    "  int every, all_six, near_sixth, shortest_first, longest_first;\n"
    "  function automatic int index_of(int c);\n"
    "    int k;\n"
    "    for (k = 0; k < 6; k++) if (codes[k] == c) return k;\n"
    "    return -1;\n"
    "  endfunction\n"
    "  initial begin\n"
    "    codes[0] = 1234; codes[1] = 1324; codes[2] = 1342;\n"
    "    codes[3] = 3412; codes[4] = 3124; codes[5] = 3142;\n"
    "    for (i = 0; i < 6; i++) counts[i] = 0;\n";

TEST(RandJoinRun, TheSixOrdersOfTheClauseAppearEvenly) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kHead) +
          "    every = 1;\n"
          "    for (i = 0; i < 600; i++) begin\n"
          "      p = 0;\n" +
          Grammar("rand join") +
          "      code = seq[0] * 1000 + seq[1] * 100 + seq[2] * 10 + seq[3];\n"
          "      if (index_of(code) < 0) every = 0;\n"
          "      else counts[index_of(code)]++;\n"
          "    end\n"
          "    all_six = 1; near_sixth = 1;\n"
          "    for (i = 0; i < 6; i++) begin\n"
          "      if (counts[i] == 0) all_six = 0;\n"
          "      if (counts[i] < 50 || counts[i] > 150) near_sixth = 0;\n"
          "    end\n"
          "    $display(\"%0d %0d %0d\", every, all_six, near_sixth);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1\n");
}

TEST(RandJoinRun, TheExpressionPrioritizesTheShortestOrTheLongest) {
  SimFixture f;
  std::string out = RunCapture(
      std::string(kHead) +
          "    for (i = 0; i < 600; i++) begin\n"
          "      p = 0;\n" +
          Grammar("rand join (0.0)") +
          "      code = seq[0] * 1000 + seq[1] * 100 + seq[2] * 10 + seq[3];\n"
          "      if (index_of(code) >= 0) counts[index_of(code)]++;\n"
          "    end\n"
          "    shortest_first = counts[0] + counts[3] > 300;\n"
          "    for (i = 0; i < 6; i++) counts[i] = 0;\n"
          "    for (i = 0; i < 600; i++) begin\n"
          "      p = 0;\n" +
          Grammar("rand join (1.0)") +
          "      code = seq[0] * 1000 + seq[1] * 100 + seq[2] * 10 + seq[3];\n"
          "      if (index_of(code) >= 0) counts[index_of(code)]++;\n"
          "    end\n"
          "    longest_first = counts[1] + counts[2] + counts[4] + counts[5] "
          "> 300;\n"
          "    $display(\"%0d %0d\", shortest_first, longest_first);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1\n");
}

TEST(RandJoinRun, NonterminalsAreInterleavedToDepthOne) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int i, p, seq[4], adjacent = 1;\n"
      "  initial begin\n"
      "    for (i = 0; i < 100; i++) begin\n"
      "      p = 0;\n"
      "      randsequence( TOP )\n"
      "        TOP : rand join S1 S2 ;\n"
      "        S1  : A ;\n"
      "        S2  : C D ;\n"
      "        A   : A1 A2 ;\n"
      "        A1  : { seq[p] = 1; p++; } ;\n"
      "        A2  : { seq[p] = 2; p++; } ;\n"
      "        C   : { seq[p] = 3; p++; } ;\n"
      "        D   : { seq[p] = 4; p++; } ;\n"
      "      endsequence\n"
      "      if (!((seq[0] == 1 && seq[1] == 2) || (seq[1] == 1 && seq[2] == "
      "2) || (seq[2] == 1 && seq[3] == 2))) adjacent = 0;\n"
      "    end\n"
      "    $display(\"%0d\", adjacent);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

TEST(RandJoinRun, AnExpressionOutsideZeroToOneIsReported) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int k = 0;\n"
      "  initial begin\n"
      "    randsequence (top)\n"
      "      top : rand join (2.0) s1 s2 ;\n"
      "      s1 : a b ;\n"
      "      s2 : a b ;\n"
      "      a : { k++; } ;\n"
      "      b : { k++; } ;\n"
      "    endsequence\n"
      "    $display(\"%0d\", k);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "rand join expression lies outside 0.0 to 1.0; it "
                            "needs a real number in that range",
                            5, "18.17.5"));
}

}  // namespace
