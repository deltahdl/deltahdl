#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(StringMethods, PutcReplacesFirstCharacter) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(0, \"H\");\n"
      "    n = (s == \"Hello\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, PutcReplacesLastCharacter) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(4, \"O\");\n"
      "    n = (s == \"hellO\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, PutcReplacesMiddleCharacterFromVariableIndex) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int i = 1;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(i, \"a\");\n"
      "    n = (s == \"hallo\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, PutcAcceptsNumericIntegralValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(0, 65);\n"
      "    n = (s == \"Abc\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, PutcAcceptsByteVariableValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  byte c = \"Z\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(2, c);\n"
      "    n = (s == \"abZ\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, PutcOperatesOnConcatenatedString) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = {\"he\", \"llo\"};\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(0, \"H\");\n"
      "    n = (s == \"Hello\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, PutcPreservesStringLength) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(0, \"H\");\n"
      "    n = s.len();\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 5u);
}

TEST(StringMethods, PutcIndexEqualToLengthLeavesStringUnchanged) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(5, \"X\");\n"
      "    n = (s == \"hello\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, PutcNegativeIndexLeavesStringUnchanged) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int i = -1;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(i, \"X\");\n"
      "    n = (s == \"hello\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, PutcOnEmptyStringLeavesItEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(0, \"X\");\n"
      "    n = (s == \"\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, PutcZeroValueLeavesStringUnchanged) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(0, 0);\n"
      "    n = (s == \"abc\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, PutcEquivalentToIndexedAssignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  string u = \"hello\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.putc(1, \"a\");\n"
      "    u[1] = \"a\";\n"
      "    n = (s == u);\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, PutcWritesAnElementOfAnArrayOfStrings) {
  auto v = RunAndGet(
      "module t;\n"
      "  string sq[$]; string sf[2]; string sd[]; string sk[string];\n"
      "  int n;\n"
      "  initial begin\n"
      "    sq.push_back(\"abc\"); sf[1] = \"abc\"; sd = new[1];\n"
      "    sd[0] = \"abc\"; sk[\"k\"] = \"abc\";\n"
      "    sq[0].putc(0, \"Q\"); sf[1].putc(1, \"Q\"); sd[0].putc(2, \"Q\");\n"
      "    sk[\"k\"].putc(0, \"Q\"); sk[\"k\"].putc(5, \"Z\"); sq[0].putc(1, "
      "0);\n"
      "    n = (sq[0] == \"Qbc\") + 2 * (sf[1] == \"aQc\") +\n"
      "        4 * (sd[0] == \"abQ\") + 8 * (sk[\"k\"] == \"Qbc\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 15u);
}

}  // namespace
