#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(AssocArrayNextMethod, IntKeyReturnsOneWhenSuccessorExists) {
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
      "    found = aa.first(k);\n"
      "    result = aa.next(k);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayNextMethod, IntKeyAssignsSuccessorIndex) {
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
      "    found = aa.first(k);\n"
      "    found = aa.next(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

TEST(AssocArrayNextMethod, IntKeyReturnsZeroAtLargestIndex) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[20] = 200;\n"
      "    found = aa.last(k);\n"
      "    result = aa.next(k);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayNextMethod, IntKeyIndexUnchangedWhenNoSuccessor) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[20] = 200;\n"
      "    found = aa.last(k);\n"
      "    found = aa.next(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(AssocArrayNextMethod, IntKeyReturnsZeroWhenEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int result;\n"
      "  initial result = aa.next(k);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayNextMethod, IntKeyArgumentNeedNotBeStored) {
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
      "    k = 20;\n"
      "    found = aa.next(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

TEST(AssocArrayNextMethod, NarrowIndexAssignsSuccessor) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[byte unsigned];\n"
      "  byte unsigned ix;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[50] = 1;\n"
      "    aa[200] = 2;\n"
      "    found = aa.first(ix);\n"
      "    found = aa.next(ix);\n"
      "    result = ix;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 200u);
}

TEST(AssocArrayNextMethod, StringKeyReturnsOneWhenSuccessorExists) {
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
      "    found = map.first(s);\n"
      "    result = map.next(s);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayNextMethod, StringKeyAssignsSuccessorKey) {
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
      "    found = map.first(s);\n"
      "    found = map.next(s);\n"
      "    result = map[s];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

TEST(AssocArrayNextMethod, StringKeyReturnsZeroAtGreatestKey) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"apple\"] = 1;\n"
      "    map[\"cherry\"] = 3;\n"
      "    found = map.last(s);\n"
      "    result = map.next(s);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayNextMethod, StringKeyArgumentNeedNotBeStored) {
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
      "    found = map.next(s);\n"
      "    result = map[s];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(AssocArrayNextMethod, StringKeyIndexUnchangedWhenNoSuccessor) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"apple\"] = 1;\n"
      "    map[\"cherry\"] = 3;\n"
      "    found = map.last(s);\n"
      "    found = map.next(s);\n"
      "    result = map[s];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(AssocArrayNextMethod, StringKeyReturnsZeroWhenEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int result;\n"
      "  initial result = map.next(s);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayNextMethod, DoWhileTraversalVisitsEveryEntry) {
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
      "    found = map.first(k);\n"
      "    do result = result + map[k];\n"
      "    while (map.next(k));\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 60u);
}

TEST(AssocArrayNextMethod, DoWhileTraversalVisitsEveryEntryOfAClassProperty) {
  uint64_t v = RunAndGet(
      "class C;\n"
      "  int map[int];\n"
      "  function int total();\n"
      "    int k;\n"
      "    int sum = 0;\n"
      "    map[1] = 10;\n"
      "    map[2] = 20;\n"
      "    map[3] = 30;\n"
      "    if (map.first(k))\n"
      "      do sum = sum + map[k];\n"
      "      while (map.next(k));\n"
      "    return sum;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    result = c.total();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 60u);
}

}  // namespace
