#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(AssocArrayAssignment, CopiesEntries_IntKeyed) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[int];\n"
      "  int dst[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    src[1] = 10;\n"
      "    src[2] = 20;\n"
      "    dst = src;\n"
      "    result = dst[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(AssocArrayAssignment, CopiesEntries_StringKeyed) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[string];\n"
      "  int dst[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    src[\"hello\"] = 42;\n"
      "    dst = src;\n"
      "    result = dst[\"hello\"];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(AssocArrayAssignment, ClearsTargetEntries) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[int];\n"
      "  int dst[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    dst[99] = 999;\n"
      "    dst[100] = 1000;\n"
      "    src[1] = 10;\n"
      "    dst = src;\n"
      "    result = dst.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayAssignment, SourceUnchangedAfterCopy) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[int];\n"
      "  int dst[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    src[1] = 42;\n"
      "    dst = src;\n"
      "    dst[1] = 100;\n"
      "    result = src[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(AssocArrayAssignment, EmptySourceClearsTarget) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[int];\n"
      "  int dst[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    dst[1] = 10;\n"
      "    dst[2] = 20;\n"
      "    dst = src;\n"
      "    result = dst.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayAssignment, AllEntriesCopied) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[int];\n"
      "  int dst[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    src[1] = 10;\n"
      "    src[2] = 20;\n"
      "    src[3] = 30;\n"
      "    dst = src;\n"
      "    result = dst[1] + dst[2] + dst[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 60u);
}

}  // namespace
