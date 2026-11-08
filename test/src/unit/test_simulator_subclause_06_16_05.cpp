#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(StringMethods, TolowerConvertsUppercaseToLowercase) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"HELLO\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    n = (u == \"hello\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, TolowerLeavesLowercaseUnchanged) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"world\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    n = (u == \"world\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, TolowerConvertsMixedCase) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"HeLLo\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    n = (u == \"hello\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, TolowerPreservesNonAlphabetic) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"A1-B2 C!\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    n = (u == \"a1-b2 c!\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, TolowerOnEmptyStringYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, TolowerOnDefaultInitializedYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, TolowerOnConcatenatedOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = {\"FOO\", \"BAR\"};\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    n = (u == \"foobar\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, TolowerFollowsProceduralReassignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"AB\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s = \"XYZ\";\n"
      "    u = s.tolower();\n"
      "    n = (u == \"xyz\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, TolowerOnCastFromIntegral) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] b = 16'h4869;\n"
      "  string s = string'(b);\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    n = (u == \"hi\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, TolowerLeavesSourceUnchanged) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"HELLO\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    n = (s == \"HELLO\") && (u == \"hello\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, TolowerResultUsableAsStringOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"GO\";\n"
      "  string u;\n"
      "  string w;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.tolower();\n"
      "    w = {u, \"!\"};\n"
      "    n = (w == \"go!\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

}  // namespace
