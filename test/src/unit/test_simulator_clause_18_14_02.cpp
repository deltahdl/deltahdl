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

// "Each thread is seeded with a unique value, determined solely by its
// parent." Two sibling threads forked from the same parent must obtain
// distinct random streams; with high probability their first draws differ.
TEST(ThreadStability, ForkedSiblingsHaveDistinctStreams) {
  auto vals = RunSeededAndRead(
      "module t;\n"
      "  int unsigned a;\n"
      "  int unsigned b;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = $urandom;\n"
      "      b = $urandom;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      {"a", "b"});
  EXPECT_NE(vals[0], vals[1]);
}

// The §18.14.2 uniqueness guarantee scales with the number of siblings; a
// fork that produces many children must give each of them its own stream so
// that no two collide.
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
