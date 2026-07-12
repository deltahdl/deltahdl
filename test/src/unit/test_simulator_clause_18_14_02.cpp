#include "fixture_simulator.h"
#include "helpers_fork_urandom_programs.h"
#include "helpers_seeded_run.h"
#include "simulator/process.h"

using namespace delta;

namespace {

// "Random values returned from the $urandom and $urandom_range system calls,
// std::randomize() scope randomization method, and shuffle() array
// manipulation method are independent of thread execution order." Running the
// fork program twice from the same starting state must yield the same draws,
// proving the values do not depend on the scheduler's interleaving choices.
TEST(ThreadStability, ForkedUrandomDrawsAreReplayable) {
  auto run = [](uint64_t& a, uint64_t& b, uint64_t& c) {
    auto vals = RunSeededAndRead(
        "module t;\n"
        "  int unsigned a;\n"
        "  int unsigned b;\n"
        "  int unsigned c;\n"
        "  initial begin\n"
        "    fork\n"
        "      a = $urandom;\n"
        "      b = $urandom;\n"
        "      c = $urandom;\n"
        "    join\n"
        "  end\n"
        "endmodule\n",
        {"a", "b", "c"});
    a = vals[0];
    b = vals[1];
    c = vals[2];
  };
  uint64_t a1 = 0, b1 = 0, c1 = 0;
  uint64_t a2 = 0, b2 = 0, c2 = 0;
  run(a1, b1, c1);
  run(a2, b2, c2);
  EXPECT_EQ(a1, a2);
  EXPECT_EQ(b1, b2);
  EXPECT_EQ(c1, c2);
}

// §18.14.2 lists $urandom_range alongside $urandom among the system calls whose
// returned values are independent of thread execution order. Two forked threads
// each draw a ranged value; replaying the fork from the same starting state
// must reproduce both draws, so each thread's value is fixed by its own
// hierarchically seeded stream rather than by the scheduler's interleaving.
TEST(ThreadStability, ForkedUrandomRangeDrawsAreReplayable) {
  auto run = [](uint64_t& a, uint64_t& b) {
    auto vals = RunSeededAndRead(
        "module t;\n"
        "  int unsigned a;\n"
        "  int unsigned b;\n"
        "  initial begin\n"
        "    fork\n"
        "      a = $urandom_range(1000000);\n"
        "      b = $urandom_range(1000000);\n"
        "    join\n"
        "  end\n"
        "endmodule\n",
        {"a", "b"});
    a = vals[0];
    b = vals[1];
  };
  uint64_t a1 = 0, b1 = 0, a2 = 0, b2 = 0;
  run(a1, b1);
  run(a2, b2);
  EXPECT_EQ(a1, a2);
  EXPECT_EQ(b1, b2);
}

// "Each thread is seeded with a unique value, determined solely by its
// parent." A fork that produces several children must give each of them its
// own stream so that no two collide -- checked here across four siblings, whose
// pairwise-distinct first draws also cover the minimal two-sibling case.
TEST(ThreadStability, ManyForkedSiblingsHaveDistinctStreams) {
  auto vals = RunFourForkedSiblingUrandom();
  auto a = vals[0];
  auto b = vals[1];
  auto c = vals[2];
  auto d = vals[3];
  EXPECT_NE(a, b);
  EXPECT_NE(a, c);
  EXPECT_NE(a, d);
  EXPECT_NE(b, c);
  EXPECT_NE(b, d);
  EXPECT_NE(c, d);
}

// "When a thread is created, its random state is initialized using the next
// random value from the parent thread as a seed." Calling srandom() on the
// parent before the fork changes the seed material the children inherit, so
// the children's draws shift accordingly.
TEST(ThreadStability, HierarchicalSeedingFromParent) {
  auto vals1 = RunParentSeededTwoForkUrandom(/*parent_seed=*/1);
  auto vals2 = RunParentSeededTwoForkUrandom(/*parent_seed=*/2);
  EXPECT_NE(vals1[0], vals2[0]);
  EXPECT_NE(vals1[1], vals2[1]);
}

// Edge case: independence must hold across multiple fork levels. A draw made
// in a grandchild thread must leave the grandparent's stream untouched, so
// the grandparent's later draw is identical whether or not the grandchild
// drew at all.
TEST(ThreadStability, NestedForkGrandchildDoesNotPerturbGrandparent) {
  auto run = [](bool with_grandchild_draw, uint64_t& outer_after) {
    std::string src = std::string(
        "module t;\n"
        "  int unsigned outer;\n"
        "  initial begin\n"
        "    fork\n"
        "      begin\n"
        "        fork\n"
        "          begin\n"
        "            int unsigned g;\n");
    src += with_grandchild_draw ? "            g = $urandom;\n"
                                : "            g = 0;\n";
    src += std::string(
        "          end\n"
        "        join\n"
        "      end\n"
        "    join\n"
        "    outer = $urandom;\n"
        "  end\n"
        "endmodule\n");
    outer_after = RunSeededAndRead(src, {"outer"})[0];
  };
  uint64_t with = 0, without = 0;
  run(/*with_grandchild_draw=*/true, with);
  run(/*with_grandchild_draw=*/false, without);
  EXPECT_EQ(with, without);
}

// §18.14.2 lists randcase among the constructs whose branch selection is
// independent of thread execution order. Two forked threads running an
// identical randcase, replayed from the same starting state, must pick the
// same branches both times.
TEST(ThreadStability, ForkedRandcaseSelectionsAreReplayable) {
  auto run = [](uint64_t& a, uint64_t& b) {
    auto vals = RunSeededAndRead(
        "module t;\n"
        "  int unsigned a;\n"
        "  int unsigned b;\n"
        "  initial begin\n"
        "    fork\n"
        "      randcase\n"
        "        1 : a = 1;\n"
        "        1 : a = 2;\n"
        "        1 : a = 3;\n"
        "        1 : a = 4;\n"
        "      endcase\n"
        "      randcase\n"
        "        1 : b = 10;\n"
        "        1 : b = 20;\n"
        "        1 : b = 30;\n"
        "        1 : b = 40;\n"
        "      endcase\n"
        "    join\n"
        "  end\n"
        "endmodule\n",
        {"a", "b"});
    a = vals[0];
    b = vals[1];
  };
  uint64_t a1 = 0, b1 = 0, a2 = 0, b2 = 0;
  run(a1, b1);
  run(a2, b2);
  EXPECT_EQ(a1, a2);
  EXPECT_EQ(b1, b2);
}

// §18.14.2 lists randsequence alongside randcase among the constructs whose
// branch selection is independent of thread execution order. Two forked threads
// each run a randsequence that picks one of four alternatives at random;
// replaying the fork from the same starting state must reproduce both threads'
// selections, so the choices do not depend on the scheduler's interleaving.
TEST(ThreadStability, ForkedRandsequenceSelectionsAreReplayable) {
  auto run = [](uint64_t& a, uint64_t& b) {
    auto vals = RunSeededAndRead(
        "module t;\n"
        "  int unsigned a;\n"
        "  int unsigned b;\n"
        "  initial begin\n"
        "    fork\n"
        "      randsequence(main)\n"
        "        main : one | two | three | four;\n"
        "        one   : { a = 1; };\n"
        "        two   : { a = 2; };\n"
        "        three : { a = 3; };\n"
        "        four  : { a = 4; };\n"
        "      endsequence\n"
        "      randsequence(main)\n"
        "        main : one | two | three | four;\n"
        "        one   : { b = 10; };\n"
        "        two   : { b = 20; };\n"
        "        three : { b = 30; };\n"
        "        four  : { b = 40; };\n"
        "      endsequence\n"
        "    join\n"
        "  end\n"
        "endmodule\n",
        {"a", "b"});
    a = vals[0];
    b = vals[1];
  };
  uint64_t a1 = 0, b1 = 0, a2 = 0, b2 = 0;
  run(a1, b1);
  run(a2, b2);
  EXPECT_EQ(a1, a2);
  EXPECT_EQ(b1, b2);
}

// "Random values returned from ... the shuffle() array manipulation method are
// independent of thread execution order." Two forked siblings each shuffle
// their own array and record the resulting first element. Replaying the fork
// from the same starting state must reproduce both siblings' shuffles, so the
// permutation each thread draws is fixed by its own hierarchically seeded
// stream rather than by the scheduler.
TEST(ThreadStability, ForkedShuffleResultsAreReplayable) {
  auto run = [](uint64_t& a, uint64_t& b) {
    auto vals = RunSeededAndRead(
        "module t;\n"
        "  int arr_a[] = '{10, 20, 30, 40, 50, 60, 70, 80};\n"
        "  int arr_b[] = '{10, 20, 30, 40, 50, 60, 70, 80};\n"
        "  int unsigned a;\n"
        "  int unsigned b;\n"
        "  initial begin\n"
        "    fork\n"
        "      begin arr_a.shuffle(); a = arr_a[0]; end\n"
        "      begin arr_b.shuffle(); b = arr_b[0]; end\n"
        "    join\n"
        "  end\n"
        "endmodule\n",
        {"a", "b"});
    a = vals[0];
    b = vals[1];
  };
  uint64_t a1 = 0, b1 = 0, a2 = 0, b2 = 0;
  run(a1, b1);
  run(a2, b2);
  EXPECT_EQ(a1, a2);
  EXPECT_EQ(b1, b2);
}

// "Each thread has an independent RNG for all randomization system calls
// invoked from that thread." A draw inside a forked thread must not advance
// the parent's RNG state -- the parent's subsequent draw is taken from its
// own stream, unaffected by the child.
TEST(ThreadStability, ChildDrawDoesNotAdvanceParentRng) {
  auto run = [](bool with_child_draw, uint64_t& parent_after) {
    std::string src = std::string(
        "module t;\n"
        "  int unsigned a;\n"
        "  int unsigned b;\n"
        "  initial begin\n"
        "    fork\n");
    if (with_child_draw) {
      src += "      a = $urandom;\n";
    } else {
      src += "      a = 0;\n";
    }
    src += std::string(
        "    join\n"
        "    b = $urandom;\n"
        "  end\n"
        "endmodule\n");
    parent_after = RunSeededAndRead(src, {"b"})[0];
  };
  uint64_t with = 0, without = 0;
  run(/*with_child_draw=*/true, with);
  run(/*with_child_draw=*/false, without);
  EXPECT_EQ(with, without);
}

}  // namespace
