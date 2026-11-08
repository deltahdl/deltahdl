#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(AssocArrayLastMethod, IntKeyReturnsOneWhenNonEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[30] = 300;\n"
      "    aa[20] = 200;\n"
      "    result = aa.last(k);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayLastMethod, IntKeyAssignsLargestIndex) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int found;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[30] = 300;\n"
      "    aa[20] = 200;\n"
      "    found = aa.last(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

TEST(AssocArrayLastMethod, IntKeyReturnsZeroWhenEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  int result;\n"
      "  initial result = aa.last(k);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayLastMethod, NarrowIndexAssignsLargestIndex) {
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
      "    result = ix;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 200u);
}

TEST(AssocArrayLastMethod, StringKeyReturnsOneWhenNonEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int result;\n"
      "  initial begin\n"
      "    map[\"apple\"] = 1;\n"
      "    map[\"cherry\"] = 3;\n"
      "    result = map.last(s);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayLastMethod, StringKeyAssignsGreatestKey) {
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
      "    result = map[s];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(AssocArrayLastMethod, StringKeyReturnsZeroWhenEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int result;\n"
      "  initial result = map.last(s);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayLastMethod, IfConditionTakesBranchWhenNonEmpty) {
  uint64_t v = RunAndGet(
      "module t;\n"
      "  int map[string];\n"
      "  string s;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    map[\"x\"] = 9;\n"
      "    if (map.last(s))\n"
      "      result = map[s];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

}  // namespace
