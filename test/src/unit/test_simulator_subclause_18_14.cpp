#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// The five kinds of draw 18.14 lists as randomly stable, taken from the
// running thread's RNG by one task: $urandom, $urandom_range, shuffle(),
// randcase and randsequence.
const char* const kDrawFive =
    "  int arr[8];\n"
    "  int unsigned u, r;\n"
    "  int f, c, q;\n"
    "  task automatic draw_five();\n"
    "    int j;\n"
    "    u = $urandom;\n"
    "    r = $urandom_range(1000);\n"
    "    for (j = 0; j < 8; j++) arr[j] = j + 1;\n"
    "    arr.shuffle();\n"
    "    f = arr[0];\n"
    "    randcase\n"
    "      1: c = 1;\n"
    "      1: c = 2;\n"
    "      1: c = 3;\n"
    "    endcase\n"
    "    randsequence(main)\n"
    "      main : one | two | three;\n"
    "      one : { q = 1; };\n"
    "      two : { q = 2; };\n"
    "      three : { q = 3; };\n"
    "    endsequence\n"
    "  endtask\n";

// 18.14: the RNG is localized to threads and objects, so a thread seeded with
// 11 and drawn from through every kind the clause lists returns the same nine
// values whether or not two objects randomize between, and seeded with 12 it
// returns another first value, as the design test/src/e2e/random_stability.sv
// runs it.
TEST(RandomStabilityRun,
     AThreadsSequenceIsUntouchedByObjectsAndSelectedBySeed) {
  SimFixture f;
  std::string out = RunCapture(
      std::string("module t;\n"
                  "  class Packet;\n"
                  "    rand bit [15:0] payload;\n"
                  "  endclass\n"
                  "  Packet a, b;\n"
                  "  process p;\n"
                  "  int i, k, agree = 0, changed;\n"
                  "  int unsigned u1, r1, t1[4], t2[4];\n"
                  "  int f1, c1, q1;\n") +
          kDrawFive +
          "  initial begin\n"
          "    a = new; b = new;\n"
          "    p = process::self();\n"
          "    p.srandom(11);\n"
          "    draw_five();\n"
          "    u1 = u; r1 = r; f1 = f; c1 = c; q1 = q;\n"
          "    for (i = 0; i < 4; i++) t1[i] = $urandom;\n"
          "    p.srandom(11);\n"
          "    a.srandom(7);\n"
          "    for (i = 0; i < 4; i++) k = a.randomize();\n"
          "    for (i = 0; i < 4; i++) k = b.randomize();\n"
          "    draw_five();\n"
          "    for (i = 0; i < 4; i++) t2[i] = $urandom;\n"
          "    if (u == u1) agree++;\n"
          "    if (r == r1) agree++;\n"
          "    if (f == f1) agree++;\n"
          "    if (c == c1) agree++;\n"
          "    if (q == q1) agree++;\n"
          "    for (i = 0; i < 4; i++) if (t1[i] == t2[i]) agree++;\n"
          "    p.srandom(12);\n"
          "    draw_five();\n"
          "    changed = u != u1;\n"
          "    $display(\"%0d %0d\", agree, changed);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "9 1\n");
}

// 18.14: the sequence a thread returns is independent of the RNG in other
// threads, so a forked thread seeded with 3 returns the same nine values
// beside a thread that draws nothing and beside one that draws a hundred and
// runs every kind the clause lists, as the design
// test/src/e2e/random_stability.sv runs it.
TEST(RandomStabilityRun, AThreadsSequenceIsUntouchedByAnotherThread) {
  SimFixture f;
  std::string out = RunCapture(
      std::string("module t;\n"
                  "  int i, agree = 0;\n"
                  "  int unsigned u1, r1, t1[4], t2[4], busy[100];\n"
                  "  int f1, c1, q1;\n") +
          kDrawFive +
          "  initial begin\n"
          "    fork\n"
          "      begin\n"
          "        process quiet = process::self();\n"
          "        quiet.srandom(5);\n"
          "      end\n"
          "      begin\n"
          "        process m = process::self();\n"
          "        m.srandom(3);\n"
          "        draw_five();\n"
          "        u1 = u; r1 = r; f1 = f; c1 = c; q1 = q;\n"
          "        for (int j = 0; j < 4; j++) t1[j] = $urandom;\n"
          "      end\n"
          "    join\n"
          "    fork\n"
          "      begin\n"
          "        process noisy = process::self();\n"
          "        noisy.srandom(5);\n"
          "        for (int j = 0; j < 100; j++) busy[j] = $urandom;\n"
          "        draw_five();\n"
          "      end\n"
          "      begin\n"
          "        process m = process::self();\n"
          "        m.srandom(3);\n"
          "        draw_five();\n"
          "        for (int j = 0; j < 4; j++) t2[j] = $urandom;\n"
          "      end\n"
          "    join\n"
          "    if (u == u1) agree++;\n"
          "    if (r == r1) agree++;\n"
          "    if (f == f1) agree++;\n"
          "    if (c == c1) agree++;\n"
          "    if (q == q1) agree++;\n"
          "    for (i = 0; i < 4; i++) if (t1[i] == t2[i]) agree++;\n"
          "    $display(\"%0d\", agree);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "9\n");
}

// 18.14: the RNG of an object is its own, so an object seeded with 7 returns
// the same four randomize() values whether or not its thread and another
// object draw between, and seeded with 8 it returns others, as the design
// test/src/e2e/random_stability.sv runs it.
TEST(RandomStabilityRun,
     AnObjectsSequenceIsUntouchedByItsThreadAndAnotherObject) {
  SimFixture f;
  std::string out = RunCapture(
      std::string("module t;\n"
                  "  class Packet;\n"
                  "    rand bit [15:0] payload;\n"
                  "  endclass\n"
                  "  Packet a, b;\n"
                  "  int i, k, agree = 0, changed = 0;\n"
                  "  bit [15:0] s1[4], s2[4], s3[4];\n") +
          kDrawFive +
          "  initial begin\n"
          "    a = new; b = new;\n"
          "    a.srandom(7);\n"
          "    for (i = 0; i < 4; i++) begin k = a.randomize(); s1[i] = "
          "a.payload; end\n"
          "    a.srandom(7);\n"
          "    for (i = 0; i < 8; i++) k = b.randomize();\n"
          "    for (i = 0; i < 8; i++) k = $urandom;\n"
          "    draw_five();\n"
          "    for (i = 0; i < 4; i++) begin k = a.randomize(); s2[i] = "
          "a.payload; end\n"
          "    for (i = 0; i < 4; i++) if (s1[i] == s2[i]) agree++;\n"
          "    a.srandom(8);\n"
          "    for (i = 0; i < 4; i++) begin k = a.randomize(); s3[i] = "
          "a.payload; end\n"
          "    for (i = 0; i < 4; i++) if (s1[i] != s3[i]) changed = 1;\n"
          "    $display(\"%0d %0d\", agree, changed);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "4 1\n");
}

}  // namespace
