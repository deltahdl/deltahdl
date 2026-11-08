#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(AssocMethods, AssocArgByValueEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  function automatic int read_first(int x[int]);\n"
      "    return x[1];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    aa[1] = 55;\n"
      "    aa[2] = 66;\n"
      "    result = read_first(aa);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 55u);
}

TEST(AssocMethods, AssocArgCallerUnchangedEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int dummy;\n"
      "  int result;\n"
      "  function automatic int mutate(int x[int]);\n"
      "    x[1] = 999;\n"
      "    return 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    aa[1] = 42;\n"
      "    dummy = mutate(aa);\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(AssocMethods, AssocArgStringKeyByValueEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[string];\n"
      "  int result;\n"
      "  function automatic int read_key(int x[string]);\n"
      "    return x[\"k\"];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    aa[\"k\"] = 77;\n"
      "    result = read_key(aa);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 77u);
}

TEST(AssocMethods, AssocArgStringKeyCallerUnchangedEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[string];\n"
      "  int dummy;\n"
      "  int result;\n"
      "  function automatic int mutate(int x[string]);\n"
      "    x[\"k\"] = 999;\n"
      "    return 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    aa[\"k\"] = 12;\n"
      "    dummy = mutate(aa);\n"
      "    result = aa[\"k\"];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 12u);
}

TEST(AssocMethods, AssocArgByValueThroughTaskEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  task automatic read(input int x[int], output int r);\n"
      "    r = x[1];\n"
      "  endtask\n"
      "  initial begin\n"
      "    aa[1] = 88;\n"
      "    read(aa, result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 88u);
}

}  // namespace
