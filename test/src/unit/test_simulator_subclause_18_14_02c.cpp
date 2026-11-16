#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunSrc(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

std::string Replace(std::string text, const std::string& name) {
  for (std::size_t at = text.find('@'); at != std::string::npos;
       at = text.find('@', at + name.size())) {
    text.replace(at, 1, name);
  }
  return text;
}

std::string ForkInOrder(const std::string& draw, const char* first,
                        const char* second, int delay_first, int delay_second) {
  return "    p.srandom(5);\n"
         "    fork\n"
         "      begin\n"
         "        #" +
         std::to_string(delay_first) + ";\n" + Replace(draw, first) +
         "      end\n"
         "      begin\n"
         "        #" +
         std::to_string(delay_second) + ";\n" + Replace(draw, second) +
         "      end\n"
         "    join\n";
}

std::string OrderProgram(const std::string& decls, const std::string& draw) {
  return "module t;\n"
         "  process p;\n" +
         Replace(decls, "a1") + Replace(decls, "b1") + Replace(decls, "a2") +
         Replace(decls, "b2") +
         "  initial begin\n"
         "    p = process::self();\n" +
         ForkInOrder(draw, "a1", "b1", 0, 1) +
         ForkInOrder(draw, "a2", "b2", 1, 0) +
         "    $display(\"%0d %0d\", a1 == a2, b1 == b2);\n"
         "  end\n"
         "endmodule\n";
}

TEST(ThreadStabilityCases, UrandomRangeDrawsAlikeInAnotherOrder) {
  EXPECT_EQ(RunSrc(OrderProgram("  int unsigned @;\n",
                                "        @ = $urandom_range(1000000);\n")),
            "1 1\n");
}

TEST(ThreadStabilityCases, ScopeRandomizeDrawsAlikeInAnotherOrder) {
  EXPECT_EQ(RunSrc(OrderProgram("  bit [31:0] @;\n",
                                "        void'(std::randomize(@));\n")),
            "1 1\n");
}

TEST(ThreadStabilityCases, ShuffleGivesTheSamePermutationInAnotherOrder) {
  EXPECT_EQ(
      RunSrc(OrderProgram("  int @;\n"
                          "  int @_q[8] = '{0, 1, 2, 3, 4, 5, 6, 7};\n",
                          "        @_q.shuffle();\n"
                          "        @ = 0;\n"
                          "        foreach (@_q[i]) @ = @ * 8 + @_q[i];\n")),
      "1 1\n");
}

TEST(ThreadStabilityCases, RandcasePicksTheSameBranchesInAnotherOrder) {
  EXPECT_EQ(RunSrc(OrderProgram("  int @ = 0;\n",
                                "        repeat (12)\n"
                                "          randcase\n"
                                "            1: @ = @ * 4 + 0;\n"
                                "            1: @ = @ * 4 + 1;\n"
                                "            1: @ = @ * 4 + 2;\n"
                                "            1: @ = @ * 4 + 3;\n"
                                "          endcase\n")),
            "1 1\n");
}

TEST(ThreadStabilityCases, RandsequencePicksTheSameProductionsInAnotherOrder) {
  EXPECT_EQ(RunSrc(OrderProgram("  int @ = 0;\n",
                                "        randsequence (main)\n"
                                "          main : x x x x x x x x x x x x;\n"
                                "          x : zero | one | two | three;\n"
                                "          zero : { @ = @ * 4 + 0; };\n"
                                "          one : { @ = @ * 4 + 1; };\n"
                                "          two : { @ = @ * 4 + 2; };\n"
                                "          three : { @ = @ * 4 + 3; };\n"
                                "        endsequence\n")),
            "1 1\n");
}

std::string ChildSeedProgram(const char* join_keyword) {
  return std::string(
             "module t;\n"
             "  process p;\n"
             "  int unsigned got, want, s1;\n"
             "  initial begin\n"
             "    p = process::self();\n"
             "    p.srandom(5);\n"
             "    fork\n"
             "      got = $urandom;\n"
             "    ") +
         join_keyword +
         "\n"
         "    wait fork;\n"
         "    p.srandom(5);\n"
         "    s1 = $urandom;\n"
         "    fork\n"
         "      begin\n"
         "        process q;\n"
         "        q = process::self();\n"
         "        q.srandom(s1);\n"
         "        want = $urandom;\n"
         "      end\n"
         "    join\n"
         "    $display(\"%0d\", got == want);\n"
         "  end\n"
         "endmodule\n";
}

TEST(ThreadStabilityCases, AJoinAnyChildIsSeededWithTheParentsNextValue) {
  EXPECT_EQ(RunSrc(ChildSeedProgram("join_any")), "1\n");
}

TEST(ThreadStabilityCases, AJoinNoneChildIsSeededWithTheParentsNextValue) {
  EXPECT_EQ(RunSrc(ChildSeedProgram("join_none")), "1\n");
}

TEST(ThreadStabilityCases, UrandomInAClassMethodDrawsFromTheCallingThread) {
  EXPECT_EQ(RunSrc("class C;\n"
                   "  function int unsigned draw();\n"
                   "    return $urandom;\n"
                   "  endfunction\n"
                   "endclass\n"
                   "module t;\n"
                   "  int unsigned a, b, c;\n"
                   "  initial begin\n"
                   "    static C o = new;\n"
                   "    process p;\n"
                   "    p = process::self();\n"
                   "    o.srandom(1);\n"
                   "    p.srandom(5);\n"
                   "    a = o.draw();\n"
                   "    o.srandom(2);\n"
                   "    p.srandom(5);\n"
                   "    b = o.draw();\n"
                   "    p.srandom(5);\n"
                   "    c = $urandom;\n"
                   "    $display(\"%0d %0d\", a == b, a == c);\n"
                   "  end\n"
                   "endmodule\n"),
            "1 1\n");
}

}  // namespace
