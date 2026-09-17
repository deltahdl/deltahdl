#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// The clause's fork: a thread seeding itself with 100 before drawing x, one
// drawing y before seeding itself with 200, and one drawing z as the sum of
// two values. `kDelayed` runs the first two threads' draws after delays of 2
// and 1, so the threads run in the reverse order.
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

// 18.14.2 thread locality: the values x, y and z of the clause's fork are
// independent of the order of thread execution, so the fork run again with
// its threads delayed into the reverse order returns the same three, as the
// design test/src/e2e/thread_stability.sv runs it.
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

// 18.14.2 hierarchical seeding: each of the three forked threads has its
// random state initialized with the next random value of the parent as a
// seed, so x is the first value of a thread seeded with 100, and y and z are
// what threads seeded by hand with the parent's second and third next values
// return, as the design test/src/e2e/thread_stability.sv runs it.
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

// 18.14.2: the root of a thread execution subtree determines the seeding of
// its children, so a subtree whose root seeds itself with 77 before forking
// three threads and drawing once more returns the same four values forked
// from two places of the parent, seven draws apart, as the design
// test/src/e2e/thread_stability.sv runs it.
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
