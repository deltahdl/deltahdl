#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(StringMethods, ToupperConvertsLowercaseToUppercase) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    n = (u == \"HELLO\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, ToupperLeavesUppercaseUnchanged) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"WORLD\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    n = (u == \"WORLD\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, ToupperConvertsMixedCase) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"HeLLo\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    n = (u == \"HELLO\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, ToupperPreservesNonAlphabetic) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"a1-b2 c!\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    n = (u == \"A1-B2 C!\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, ToupperOnEmptyStringYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, ToupperOnDefaultInitializedYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, ToupperOnConcatenatedOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = {\"foo\", \"bar\"};\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    n = (u == \"FOOBAR\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, ToupperFollowsProceduralReassignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"ab\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s = \"xyz\";\n"
      "    u = s.toupper();\n"
      "    n = (u == \"XYZ\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, ToupperOnCastFromIntegral) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] b = 16'h4869;\n"
      "  string s = string'(b);\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    n = (u == \"HI\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, ToupperLeavesSourceUnchanged) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    n = (s == \"hello\") && (u == \"HELLO\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, ToupperResultUsableAsStringOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"go\";\n"
      "  string u;\n"
      "  string w;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.toupper();\n"
      "    w = {u, \"!\"};\n"
      "    n = (w == \"GO!\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

}  // namespace
