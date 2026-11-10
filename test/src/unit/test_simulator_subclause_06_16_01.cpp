#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
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

TEST(StringLenSim, LenCountsTheCharactersWhereverTheStringIsReached) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "package p; string ps = \"pkg\"; endpackage\n"
          "typedef struct { string s; int n; } st_t;\n"
          "class K;\n"
          "  string ks = \"klass\";\n"
          "  static string ss = \"st\";\n"
          "  function int klen(); return ks.len(); endfunction\n"
          "endclass\n"
          "module t;\n"
          "  string q [$], aa [int], da [];\n"
          "  st_t st;\n"
          "  K k = new;\n"
          "  function string f(); return \"hello\"; endfunction\n"
          "  initial begin\n"
          "    q.push_back(\"queue\"); aa[3] = \"assoc7\";\n"
          "    da = new[1]; da[0] = \"dy\"; st.s = \"struct\";\n"
          "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d %0d\", p::ps.len(),\n"
          "      k.ks.len(), K::ss.len(), k.klen(), q[0].len(), aa[3].len(),\n"
          "      da[0].len(), st.s.len(), f().len());\n"
          "  end\n"
          "endmodule\n",
          f),
      "3 5 2 5 5 6 2 6 5\n");
}

TEST(StringLenSim, DISABLED_LenOfAStringReachedByAHierarchicalName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; string is = \"ifc!\"; endinterface\n"
                       "module sub; string ms = \"sub!!\"; endmodule\n"
                       "module t;\n"
                       "  ifc i();\n"
                       "  sub u();\n"
                       "  string s = \"ab\";\n"
                       "  initial #1 $display(\"%0d %0d %0d\", i.is.len(),\n"
                       "                      u.ms.len(), t.s.len());\n"
                       "endmodule\n",
                       f),
            "4 5 2\n");
}

}  // namespace
