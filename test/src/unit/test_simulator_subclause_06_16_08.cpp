#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(StringMethods, SubstrMiddleRange) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello world\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(6, 10);\n"
      "    n = (u == \"world\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, SubstrSingleCharacterWhenIEqualsJ) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(2, 2);\n"
      "    n = (u == \"l\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, SubstrPrefixFromZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(0, 1);\n"
      "    n = (u == \"he\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, SubstrSuffixToLastIndex) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(3, 4);\n"
      "    n = (u == \"lo\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, SubstrEntireStringViaLen) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(0, s.len() - 1);\n"
      "    n = (u == \"hello\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, SubstrOnConcatenatedOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = {\"foo\", \"bar\"};\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(1, 4);\n"
      "    n = (u == \"ooba\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, SubstrFollowsProceduralReassignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"aaaa\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s = \"wxyz\";\n"
      "    u = s.substr(1, 2);\n"
      "    n = (u == \"xy\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, SubstrOnCastFromIntegral) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] b = 16'h4869;\n"
      "  string s = string'(b);\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(0, 1);\n"
      "    n = (u == \"Hi\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, SubstrOperandFromParameterString) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter string p = \"cat\";\n"
      "  string s = p;\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(1, 2);\n"
      "    n = (u == \"at\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, SubstrResultUsableAsStringOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello world\";\n"
      "  string u;\n"
      "  string w;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(6, 10);\n"
      "    w = {u.substr(0, 2), \"!\"};\n"
      "    n = (w == \"wor!\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, SubstrNegativeIYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(-1, 2);\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, SubstrJLessThanIYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(3, 1);\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, SubstrNegativeJYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(2, -1);\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, SubstrJBeyondLengthYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(0, 10);\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, SubstrJEqualToLengthYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(0, s.len());\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, SubstrOnEmptyStringYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(0, 0);\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, SubstrOnDefaultInitializedOperandYieldsEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    u = s.substr(0, 0);\n"
      "    n = (u == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

}  // namespace
