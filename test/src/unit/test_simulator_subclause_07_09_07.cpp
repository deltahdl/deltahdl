#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(AssocArrayPrevMethod, IntKeyReturnsOneWhenPredecessorExists) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[30] = 300;\n"
      "    aa[50] = 500;\n"
      "    found = aa.last(k);\n"
      "    result = aa.prev(k);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayPrevMethod, IntKeyAssignsPredecessorIndex) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[30] = 300;\n"
      "    aa[50] = 500;\n"
      "    found = aa.last(k);\n"
      "    found = aa.prev(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

TEST(AssocArrayPrevMethod, IntKeyReturnsZeroAtSmallestIndex) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[20] = 200;\n"
      "    found = aa.first(k);\n"
      "    result = aa.prev(k);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayPrevMethod, IntKeyIndexUnchangedWhenNoPredecessor) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[20] = 200;\n"
      "    found = aa.first(k);\n"
      "    found = aa.prev(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 10u);
}

TEST(AssocArrayPrevMethod, IntKeyReturnsZeroWhenEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int result;\n"
      "  initial result = aa.prev(k);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayPrevMethod, IntKeyArgumentNeedNotBeStored) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[30] = 300;\n"
      "    aa[50] = 500;\n"
      "    k = 40;\n"
      "    found = aa.prev(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

TEST(AssocArrayPrevMethod, IntKeyArgumentAboveAllKeysReachesLast) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[20] = 200;\n"
      "    aa[30] = 300;\n"
      "    k = 100;\n"
      "    found = aa.prev(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

TEST(AssocArrayPrevMethod, NarrowIndexAssignsPredecessor) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[byte unsigned];\n"
      "  byte unsigned ix;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[50] = 1;\n"
      "    aa[200] = 2;\n"
      "    found = aa.last(ix);\n"
      "    found = aa.prev(ix);\n"
      "    result = ix;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 50u);
}

TEST(AssocArrayPrevMethod, StringKeyReturnsOneWhenPredecessorExists) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"apple\"] = 1;\n"
      "    map[\"banana\"] = 2;\n"
      "    map[\"cherry\"] = 3;\n"
      "    found = map.last(s);\n"
      "    result = map.prev(s);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayPrevMethod, StringKeyAssignsPredecessorKey) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"apple\"] = 1;\n"
      "    map[\"banana\"] = 2;\n"
      "    map[\"cherry\"] = 3;\n"
      "    found = map.last(s);\n"
      "    found = map.prev(s);\n"
      "    result = map[s];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

TEST(AssocArrayPrevMethod, StringKeyReturnsZeroAtSmallestKey) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"apple\"] = 1;\n"
      "    map[\"cherry\"] = 3;\n"
      "    found = map.first(s);\n"
      "    result = map.prev(s);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayPrevMethod, StringKeyArgumentNeedNotBeStored) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"apple\"] = 1;\n"
      "    map[\"cherry\"] = 3;\n"
      "    s = \"banana\";\n"
      "    found = map.prev(s);\n"
      "    result = map[s];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayPrevMethod, StringKeyIndexUnchangedWhenNoPredecessor) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"apple\"] = 1;\n"
      "    map[\"cherry\"] = 3;\n"
      "    found = map.first(s);\n"
      "    found = map.prev(s);\n"
      "    result = map[s];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayPrevMethod, StringKeyReturnsZeroWhenEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int result;\n"
      "  initial result = map.prev(s);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayPrevMethod, DoWhileReverseTraversalVisitsEveryEntry) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[1] = 10;\n"
      "    map[2] = 20;\n"
      "    map[3] = 30;\n"
      "    result = 0;\n"
      "    found = map.last(k);\n"
      "    do result = result + map[k];\n"
      "    while (map.prev(k));\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 60u);
}

}  // namespace
