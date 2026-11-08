#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

const char* const kClauseFork =
    "    fork\n"
    "      begin\n"
    "        process pvar;\n"
    "        pvar = process::self();\n"
    "        pvar.srandom(100);\n"
    "        x = $urandom;\n"
    "      end\n"
    "      begin\n"
    "        process pvar;\n"
    "        pvar = process::self();\n"
    "        y = $urandom;\n"
    "        pvar.srandom(200);\n"
    "      end\n"
    "      begin\n"
    "        z = $urandom + $urandom;\n"
    "      end\n"
    "    join\n";
const char* const kDelayed =
    "    fork\n"
    "      begin\n"
    "        process pvar;\n"
    "        pvar = process::self();\n"
    "        pvar.srandom(100);\n"
    "        #2 x2 = $urandom;\n"
    "      end\n"
    "      begin\n"
    "        process pvar;\n"
    "        pvar = process::self();\n"
    "        #1 y2 = $urandom;\n"
    "        pvar.srandom(200);\n"
    "      end\n"
    "      begin\n"
    "        z2 = $urandom + $urandom;\n"
    "      end\n"
    "    join\n";

TEST(ThreadStabilityRun, TheClausesForkDrawsTheSameInAnotherOrder) {
  SimFixture f;
  std::string out =
      RunCapture(std::string("module t;\n"
                             "  process p;\n"
                             "  integer x, y, z, x2, y2, z2;\n"
                             "  int agree = 0;\n"
                             "  initial begin\n"
                             "    p = process::self();\n"
                             "    p.srandom(5);\n") +
                     kClauseFork + "    p.srandom(5);\n" + kDelayed +
                     "    if (x == x2) agree++;\n"
                     "    if (y == y2) agree++;\n"
                     "    if (z == z2) agree++;\n"
                     "    $display(\"%0d\", agree);\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_EQ(out, "3\n");
}

TEST(ThreadStabilityRun, EachThreadIsSeededWithTheParentsNextValue) {
  SimFixture f;
  std::string out =
      RunCapture(std::string("module t;\n"
                             "  process p;\n"
                             "  integer x, y, z, y2, z2, x100;\n"
                             "  int unsigned s1, s2, s3;\n"
                             "  int first, by_hand = 0;\n"
                             "  initial begin\n"
                             "    p = process::self();\n"
                             "    p.srandom(5);\n") +
                     kClauseFork +
                     "    p.srandom(100);\n"
                     "    x100 = $urandom;\n"
                     "    first = x == x100;\n"
                     "    p.srandom(5);\n"
                     "    s1 = $urandom;\n"
                     "    s2 = $urandom;\n"
                     "    s3 = $urandom;\n"
                     "    fork\n"
                     "      begin\n"
                     "        process q;\n"
                     "        q = process::self();\n"
                     "        q.srandom(s2);\n"
                     "        y2 = $urandom;\n"
                     "      end\n"
                     "      begin\n"
                     "        process q;\n"
                     "        q = process::self();\n"
                     "        q.srandom(s3);\n"
                     "        z2 = $urandom + $urandom;\n"
                     "      end\n"
                     "    join\n"
                     "    if (y == y2) by_hand++;\n"
                     "    if (z == z2) by_hand++;\n"
                     "    $display(\"%0d %0d\", first, by_hand);\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_EQ(out, "1 2\n");
}

TEST(ThreadStabilityRun, ASubtreeSeededAtItsRootDrawsAlikeFromAnywhere) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  process p;\n"
      "  int unsigned a1, a2, a3, a4, b1, b2, b3, b4;\n"
      "  int i, k, moved = 0;\n"
      "  initial begin\n"
      "    p = process::self();\n"
      "    p.srandom(5);\n"
      "    fork\n"
      "      begin\n"
      "        process r;\n"
      "        r = process::self();\n"
      "        r.srandom(77);\n"
      "        fork\n"
      "          a1 = $urandom;\n"
      "          a2 = $urandom_range(100);\n"
      "          a3 = $urandom;\n"
      "        join\n"
      "        a4 = $urandom;\n"
      "      end\n"
      "    join\n"
      "    for (i = 0; i < 7; i++) k = $urandom;\n"
      "    fork\n"
      "      begin\n"
      "        process r;\n"
      "        r = process::self();\n"
      "        r.srandom(77);\n"
      "        fork\n"
      "          b1 = $urandom;\n"
      "          b2 = $urandom_range(100);\n"
      "          b3 = $urandom;\n"
      "        join\n"
      "        b4 = $urandom;\n"
      "      end\n"
      "    join\n"
      "    if (a1 == b1) moved++;\n"
      "    if (a2 == b2) moved++;\n"
      "    if (a3 == b3) moved++;\n"
      "    if (a4 == b4) moved++;\n"
      "    $display(\"%0d\", moved);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

}  // namespace
