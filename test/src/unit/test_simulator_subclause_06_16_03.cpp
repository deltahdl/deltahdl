#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_string.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StringMethods, GetcReturnsAsciiCodeOfCharacter) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int n;\n"
      "  initial n = s.getc(1);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, static_cast<uint64_t>('e'));
}

TEST(StringMethods, GetcFirstCharacter) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int n;\n"
      "  initial n = s.getc(0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, static_cast<uint64_t>('a'));
}

TEST(StringMethods, GetcLastCharacter) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int n;\n"
      "  initial n = s.getc(2);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, static_cast<uint64_t>('c'));
}

TEST(StringMethods, GetcFromVariableIndex) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int i = 4;\n"
      "  int n;\n"
      "  initial n = s.getc(i);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, static_cast<uint64_t>('o'));
}

TEST(StringMethods, GetcIndexFromLenSelectsLastCharacter) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int n;\n"
      "  initial n = s.getc(s.len() - 1);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, static_cast<uint64_t>('o'));
}

TEST(StringMethods, GetcOnConcatenatedString) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = {\"he\", \"llo\"};\n"
      "  int n;\n"
      "  initial n = s.getc(0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, static_cast<uint64_t>('h'));
}

TEST(StringMethods, GetcFollowsProceduralReassignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"ab\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s = \"xyz\";\n"
      "    n = s.getc(1);\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, static_cast<uint64_t>('y'));
}

TEST(StringMethods, GetcOnCastFromIntegral) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] b = 16'h4869;\n"
      "  string s = string'(b);\n"
      "  int n;\n"
      "  initial n = s.getc(0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, static_cast<uint64_t>('H'));
}

TEST(StringMethods, GetcUsableAsOperandInExpression) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"abc\";\n"
      "  int n;\n"
      "  initial n = s.getc(1) - s.getc(0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, GetcIndexEqualToLengthReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hi\";\n"
      "  int n;\n"
      "  initial n = s.getc(2);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

TEST(StringMethods, GetcNegativeIndexReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hi\";\n"
      "  int i = -1;\n"
      "  int n;\n"
      "  initial n = s.getc(i);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

TEST(StringMethods, GetcEmptyStringReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  int n;\n"
      "  initial n = s.getc(0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

TEST(StringMethods, GetcDefaultInitializedReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial n = s.getc(0);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

TEST(StringMethods, GetcEquivalentToIndexedRead) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"world\";\n"
      "  int n;\n"
      "  initial n = (s.getc(2) == \"r\") && (s.getc(2) == s[2]);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, GetcEquivalentToIndexedReadOutOfBounds) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"world\";\n"
      "  int n;\n"
      "  initial n = (s.getc(5) == 0) && (s.getc(5) == s[5]);\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, GetcReturnsByteWidth) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "getc", {f.MakeIntLiteral(1)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
}

}  // namespace
