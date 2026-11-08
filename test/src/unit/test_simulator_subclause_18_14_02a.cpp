#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_fork_urandom_programs.h"
#include "helpers_seeded_run.h"

using namespace delta;

namespace {

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

TEST(ThreadStability, ForkedUrandomRangeDrawsAreReplayable) {
  ExpectForkedUrandomRangeDrawsReplay();
}

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

TEST(ThreadStability, HierarchicalSeedingFromParent) {
  auto vals1 = RunParentSeededTwoForkUrandom(1);
  auto vals2 = RunParentSeededTwoForkUrandom(2);
  EXPECT_NE(vals1[0], vals2[0]);
  EXPECT_NE(vals1[1], vals2[1]);
}

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
  run(true, with);
  run(false, without);
  EXPECT_EQ(with, without);
}

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
  run(true, with);
  run(false, without);
  EXPECT_EQ(with, without);
}

}  // namespace
