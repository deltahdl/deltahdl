#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(StringDataType,
     TheConversionsAndConcatenationsOfTheSubclauseGiveTheirValues) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n  typedef logic [15:0] r_t;\n  r_t r;\n"
          "  integer i = 2;\n  string a, b = \"\", z;\n"
          "  bit [1:4][7:0] h = \"hello\";\n  byte c = \"A\";\n"
          "  bit [10:0] bb = \"\\x41\";\n  bit [11:0] b12 = 12'ha41;\n"
          "  initial begin\n"
          "    a = {\"Hi\", b};\n    r = r_t'(a);\n    b = string'(r);\n"
          "    $display(\"%h %s %0d\", r, b, b.len());\n"
          "    b = {5{\"Hi\"}};\n    a = {i{\"Hi\"}};\n"
          "    $display(\"%s %s\", b, a);\n"
          "    a = {i{b}};\n    $display(\"%0d\", a.len());\n"
          "    a = \"Hi\";\n    a = {a, a};\n    $display(\"%s\", a);\n"
          "    a = \"cough\";\n    a[0] = \"h\";\n    a[1] = \"\\0\";\n"
          "    $display(\"%s\", a);\n"
          "    $display(\"%h %h %h\", h, c, bb);\n"
          "    z = string'(b12);\n"
          "    $display(\"%0d %0d %0d\", z.len(), z[0], z[1]);\n"
          "    z = string'(16'h4100);\n    $display(\"%s %0d\", z, z.len());\n"
          "    z = string'(24'h410042);\n    $display(\"%s\", z);\n"
          "  end\nendmodule\n",
          f),
      "4869 Hi 2\nHiHiHiHiHi HiHi\n20\nHiHi\nhough\n656c6c6f 41 041\n"
      "2 10 65\nA 1\nAB\n");
}

TEST(StringDataType,
     AnEmptyLiteralIsAZeroByteAmongLiteralsAndNothingBesideAString) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n  logic [15:0] r, r2;\n  string b, s = \"H\";\n"
          "  initial begin\n"
          "    r = {\"H\", \"\"};\n    $display(\"%h\", r);\n"
          "    b = {\"H\", \"\"};\n    $display(\"%s %0d\", b, b.len());\n"
          "    b = {\"\", \"H\", \"\"};\n    $display(\"%s %0d\", b, "
          "b.len());\n"
          "    b = {s, \"\"};\n    $display(\"%s %0d\", b, b.len());\n"
          "    $display(\"%0d %0d\", {\"H\", \"\"} == \"H\", {s, \"\"} == "
          "\"H\");\n"
          "    $display(\"%0d\", $bits({\"H\", \"\"}));\n"
          "    r2 = {2{\"\"}};\n    b = {2{\"\"}};\n"
          "    $display(\"%h %0d\", r2, b.len());\n"
          "  end\nendmodule\n",
          f),
      "4800\nH 1\nH 1\nH 1\n0 1\n16\n0000 0\n");
}

TEST(StringDataType, LiteralsAloneCompareAndReplicateAsIntegralValues) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n  string s = \"b\", q = \"abab\";\n"
                       "  initial begin\n"
                       "    $display(\"%0d %0d %0d %0d\", \"b\" > \"ab\", "
                       "s > \"ab\", \"ab\" <= \"b\", s <= \"ab\");\n"
                       "    $display(\"%0d %0d %0d\", $bits({2{\"Hi\"}}), "
                       "{2{\"ab\"}} == \"abab\", q == {2{\"ab\"}});\n"
                       "  end\nendmodule\n",
                       f),
            "0 1 0 0\n32 1 1\n");
}

TEST(StringDataType, ANonConstantZeroMultiplierGivesTheEmptyString) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n  string s = \"q\", b = \"x\";\n  int n = 0;\n"
                 "  initial begin\n    s = {n{b}};\n"
                 "    $display(\"[%s] %0d\", s, s.len());\n"
                 "    s = {n{\"ab\"}};\n    $display(\"[%s]\", s);\n"
                 "  end\nendmodule\n",
                 f),
      "[] 0\n[]\n");
}

TEST(StringDataType, ACharacterIsOneByteWideAndReadsBackIntoAByte) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n  string s = \"\\x80\";\n  byte b;\n"
                       "  initial begin\n    b = s[0];\n"
                       "    $display(\"%0d %0d\", b, $bits(s[0]));\n"
                       "  end\nendmodule\n",
                       f),
            "-128 8\n");
}

TEST(StringDataType, DISABLED_ACharacterIsASignedByteInEveryExpression) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n  string s = \"\\x80\", m = \"\\xff\";\n"
                       "  int n;\n"
                       "  function int f();\n    return m[0];\n  endfunction\n"
                       "  initial begin\n    n = s[0];\n"
                       "    $display(\"%0d %0d %0d %0d\", n, s[0] < 0, f(), "
                       "s[0] + 0);\n"
                       "  end\nendmodule\n",
                       f),
            "-128 1 -1 -128\n");
}

TEST(StringDataType, AWriteBeyondTheLastCharacterLeavesTheStringUnchanged) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n  string a = \"abc\";\n"
                 "  initial begin\n    a[3] = \"d\";\n    a[-1] = \"e\";\n"
                 "    $display(\"%s %0d %0d\", a, a[-1], a[3]);\n"
                 "  end\nendmodule\n",
                 f),
      "abc 0 0\n");
}

TEST(StringDataType, DISABLED_AWriteIntoAnEmptyStringLeavesItEmpty) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n  string e = \"\", d;\n"
                 "  initial begin\n    e[0] = \"x\";\n    d[0] = \"y\";\n"
                 "    $display(\"%0d %0d %0d\", e.len(), d.len(), e[0]);\n"
                 "  end\nendmodule\n",
                 f),
      "0 0 0\n");
}

TEST(StringDataType,
     ACharacterOfAMemberElementOrPropertyWrittenThroughAHandleIsSelected) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "class C;\n  string t = \"AB\";\n  static string ss = \"AB\";\n"
          "  function void w();\n    t[0] = \"Z\";\n  endfunction\nendclass\n"
          "string us = \"AB\";\n"
          "module t;\n  C c = new, d = new;\n"
          "  typedef struct { string s; } S;\n  S st;\n  string arr[2];\n"
          "  initial begin\n    st.s = \"XY\";\n    arr[1] = \"XY\";\n"
          "    c.w();\n    d.t[1] = \"Y\";\n    C::ss[0] = \"Q\";\n"
          "    us[1] = \"U\";\n"
          "    $display(\"%s %s %s %s %0d %0d %0d %0d\", c.t, d.t, C::ss, us, "
          "st.s[1], arr[1][1], c.t.getc(1), us[0]);\n"
          "  end\nendmodule\n",
          f),
      "ZB AY QB AU 89 89 66 65\n");
}

TEST(StringDataType,
     DISABLED_ACharacterOfAStringReachedThroughAScopeOrHierarchyIsSelected) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "class C;\n  string t = \"AB\";\n  static string ss = \"AB\";\n"
          "  function int g();\n    return t[1];\n  endfunction\nendclass\n"
          "package k;\n  string ps = \"AB\";\nendpackage\n"
          "interface ifc;\n  string s = \"AB\";\nendinterface\n"
          "module t;\n  C c = new;\n  ifc i();\n"
          "  if (1) begin : g\n    string s = \"AB\";\n  end\n"
          "  initial begin\n"
          "    $display(\"%0d %0d %0d %0d %0d %0d\", c.t[1], c.g(), C::ss[1], "
          "k::ps[1], i.s[1], g.s[1]);\n"
          "    k::ps[0] = \"P\";\n    i.s[1] = \"I\";\n    g.s[0] = \"G\";\n"
          "    $display(\"%s %s %s\", k::ps, i.s, g.s);\n"
          "  end\nendmodule\n",
          f),
      "66 66 66 66 66 66\nPB AI GB\n");
}

}  // namespace
