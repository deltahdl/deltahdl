#include <gtest/gtest.h>

#include "fixture_string.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StringMethods, LenCountsCharactersOfLiteralInit) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int n;\n"
      "  initial n = s.len();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 5u);
}

TEST(StringMethods, LenCountsCharactersNotSourceBytes) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"ab\\0cd\";\n"
      "  int n;\n"
      "  initial n = s.len();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 4u);
}

TEST(StringMethods, LenOfConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = {\"foo\", \"bar\"};\n"
      "  int n;\n"
      "  initial n = s.len();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 6u);
}

TEST(StringMethods, LenFollowsProceduralReassignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"ab\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s = \"abcdef\";\n"
      "    n = s.len();\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 6u);
}

TEST(StringMethods, LenOfCastFromIntegral) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] b = 16'h4869;\n"
      "  string s = string'(b);\n"
      "  int n;\n"
      "  initial n = s.len();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 2u);
}

TEST(StringMethods, LenUsableAsIntOperandInExpression) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"hello\";\n"
      "  int n;\n"
      "  initial n = s.len() * 2 - 1;\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 9u);
}

TEST(StringMethods, LenEmptyLiteralIsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"\";\n"
      "  int n;\n"
      "  initial n = s.len();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

TEST(StringMethods, LenDefaultInitializedIsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial n = s.len();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 0u);
}

TEST(StringMethods, LenReturnsIntWidth) {
  StringFixture f;
  f.CreateStringVar("s", "hello");
  auto* call = f.MakeMethodCall("s", "len");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

TEST(StringMethods, LenCountsCharactersOfATypedefStringAtModuleScope) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef string s_t;\n"
      "  s_t s = \"hello world\";\n"
      "  int n;\n"
      "  initial n = s.len();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 11u);
}

TEST(StringMethods, LenCountsCharactersOfATypedefStringInABlock) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef string s_t;\n"
      "  int n;\n"
      "  initial begin\n"
      "    static s_t s = \"hello world\";\n"
      "    n = s.len();\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 11u);
}

TEST(StringMethods, LenCountsCharactersOfATypedefStringInASubroutine) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef string s_t;\n"
      "  int n;\n"
      "  function int measure();\n"
      "    static s_t s = \"hello world\";\n"
      "    return s.len();\n"
      "  endfunction\n"
      "  initial n = measure();\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 11u);
}

}  // namespace
