#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
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

TEST(StringGetcSim, GetcReadsTheStringWhereverItIsReached) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "package p; string ps = \"Pkg\"; endpackage\n"
          "typedef struct { string s; int n; } st_t;\n"
          "class K; string ks = \"kLass\"; endclass\n"
          "module t;\n"
          "  string q [$];\n"
          "  st_t st;\n"
          "  K k = new;\n"
          "  function string f(); return \"hello\"; endfunction\n"
          "  initial begin\n"
          "    q.push_back(\"Queue\"); st.s = \"struct\";\n"
          "    $display(\"%0d %0d %0d %0d %0d\", p::ps.getc(0),\n"
          "      k.ks.getc(1), q[0].getc(0), st.s.getc(0), f().getc(1));\n"
          "  end\n"
          "endmodule\n",
          f),
      "80 76 81 115 101\n");
}

TEST(StringGetcSim, DISABLED_GetcReturnsASignedByte) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  string s;\n"
                       "  byte b;\n"
                       "  int x, y;\n"
                       "  initial begin\n"
                       "    s = string'(16'hFF41);\n"
                       "    b = s.getc(0);\n"
                       "    x = s.getc(0);\n"
                       "    y = s[0];\n"
                       "    $display(\"%0d %0d %0d %0d %0d %0d\", b, x, y,\n"
                       "             s.getc(0) < 0, s[0] < 0, s.getc(1) < 0);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "-1 -1 -1 1 1 0\n");
}

TEST(StringGetcSim, DISABLED_GetcOfAStringReachedByAHierarchicalName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; string is = \"ifc!\"; endinterface\n"
                       "module sub; string ms = \"Sub!\"; endmodule\n"
                       "module t;\n"
                       "  ifc i();\n"
                       "  sub u();\n"
                       "  string s = \"ab\";\n"
                       "  initial #1 $display(\"%0d %0d %0d\", i.is.getc(0),\n"
                       "                      u.ms.getc(0), t.s.getc(1));\n"
                       "endmodule\n",
                       f),
            "105 83 98\n");
}

TEST(StringGetcSim, DISABLED_GetcConvertsARealIndexToInt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  string s = \"abcd\";\n"
                       "  real r = 2.5;\n"
                       "  initial $display(\"%0d %0d %0d\", s.getc(0.6),\n"
                       "                   s.getc(-0.4), s.getc(r));\n"
                       "endmodule\n",
                       f),
            "98 97 100\n");
}

}  // namespace
