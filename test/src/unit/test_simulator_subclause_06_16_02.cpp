#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
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

TEST(StringPutcSim, PutcWritesTheStringWhereverItIsReached) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package p; string ps = \"pkg\"; endpackage\n"
                 "class K; string ks = \"klass\"; endclass\n"
                 "module t;\n"
                 "  string s = \"abcd\", q [$], aa [int], da [];\n"
                 "  K k = new;\n"
                 "  function automatic void put_ref(ref string r);\n"
                 "    r.putc(0, \"Z\");\n"
                 "  endfunction\n"
                 "  initial begin\n"
                 "    q.push_back(\"queue\"); aa[3] = \"assoc7\";\n"
                 "    da = new[1]; da[0] = \"dy\";\n"
                 "    p::ps.putc(0, \"P\"); k.ks.putc(1, \"L\"); q[0].putc(0, "
                 "\"Q\");\n"
                 "    aa[3].putc(0, \"A\"); da[0].putc(1, \"Y\"); put_ref(s);\n"
                 "    $display(\"%s %s %s %s %s %s\", p::ps, k.ks, q[0], "
                 "aa[3], da[0],\n"
                 "             s);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "Pkg kLass Queue Assoc7 dY Zbcd\n");
}

TEST(StringPutcSim, PutcTakesTheLowByteOfItsValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  string s = \"abcd\";\n"
                       "  initial begin\n"
                       "    s.putc(0, 16'h142);\n"
                       "    s.putc(1, 12'h300);\n"
                       "    s.putc(2, 8'bx);\n"
                       "    s.putc(3, -191);\n"
                       "    $display(\"%s %0d\", s, s.len());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "BbcA 4\n");
}

TEST(StringPutcSim, DISABLED_PutcWritesAStructureMemberString) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { string s; int n; } st_t;\n"
                       "module t;\n"
                       "  st_t st, sa [2];\n"
                       "  initial begin\n"
                       "    st.s = \"struct\"; sa[1].s = \"elem\";\n"
                       "    st.s.putc(0, \"S\"); sa[1].s.putc(3, \"!\");\n"
                       "    $display(\"%s %s\", st.s, sa[1].s);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "Struct ele!\n");
}

TEST(StringPutcSim, DISABLED_PutcWritesAStringReachedByAHierarchicalName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; string is = \"ifc!\"; endinterface\n"
                       "module sub; string ms = \"sub!\"; endmodule\n"
                       "module t;\n"
                       "  ifc i();\n"
                       "  sub u();\n"
                       "  string s = \"ab\";\n"
                       "  initial begin\n"
                       "    #1 i.is.putc(3, \"?\"); u.ms.putc(0, \"S\");\n"
                       "    t.s.putc(1, \"B\");\n"
                       "    $display(\"%s %s %s\", i.is, u.ms, s);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "ifc? Sub! aB\n");
}

TEST(StringPutcSim, DISABLED_PutcConvertsARealIndexToInt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  string s = \"abcd\";\n"
                       "  real r = 2.5;\n"
                       "  initial begin\n"
                       "    s.putc(0.6, \"Y\");\n"
                       "    s.putc(-0.4, \"Z\");\n"
                       "    s.putc(r, \"W\");\n"
                       "    $display(\"%s\", s);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "ZYcW\n");
}

}  // namespace
