#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(StringMethods, ItoaStoresDecimalText) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.itoa(123);\n"
      "    n = (s == \"123\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, ItoaZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.itoa(0);\n"
      "    n = (s == \"0\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, ItoaReplacesLongerExisting) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"999999\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.itoa(7);\n"
      "    n = (s == \"7\") && (s.len() == 1);\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, ItoaIsInverseOfAtoi) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int r;\n"
      "  initial begin\n"
      "    s.itoa(2024);\n"
      "    r = s.atoi();\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 2024u);
}

TEST(StringMethods, ItoaFromIntegerType) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  integer x = 89;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.itoa(x);\n"
      "    n = (s == \"89\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, ItoaFromParameter) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter int P = 42;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.itoa(P);\n"
      "    n = (s == \"42\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, ItoaFromLocalparam) {
  auto v = RunAndGet(
      "module t;\n"
      "  localparam int L = 500;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.itoa(L);\n"
      "    n = (s == \"500\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, ItoaFromExpressionArgument) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int x = 40;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.itoa(x + 2);\n"
      "    n = (s == \"42\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, ItoaResultUsedInConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  string t;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.itoa(12);\n"
      "    t = {s, \"3\"};\n"
      "    n = (t == \"123\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, ItoaStoresIntoAnElementOfAnArrayOfStrings) {
  auto v = RunAndGet(
      "module t;\n"
      "  string sq[$]; string sf[2]; string sd[]; string sk[int];\n"
      "  int n;\n"
      "  initial begin\n"
      "    sq.push_back(\"abc\"); sf[0] = \"x\"; sd = new[1]; sk[3] = \"x\";\n"
      "    sq[0].itoa(42); sf[0].itoa(1000); sd[0].itoa(7);\n"
      "    sk[3].itoa(65535);\n"
      "    n = (sq[0] == \"42\") + 2 * (sf[0] == \"1000\") +\n"
      "        4 * (sd[0] == \"7\") + 8 * (sk[3] == \"65535\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 15u);
}

TEST(StringMethods, ItoaConvertsItsArgumentToInteger) {
  auto v = RunAndGet(
      "module t;\n"
      "  string a, b, c;\n"
      "  int i = -7;\n"
      "  longint w = 64'h1_0000_0005;\n"
      "  int n;\n"
      "  initial begin\n"
      "    a.itoa(-7); b.itoa(i); c.itoa(w);\n"
      "    n = (a == \"-7\") + 2 * (b == \"-7\") + 4 * (c == \"5\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 7u);
}

TEST(StringItoaSim, ItoaWritesTheStringWhereverItIsReached) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package p; string ps = \"old\"; endpackage\n"
                 "class K; string ks = \"old\"; endclass\n"
                 "module t;\n"
                 "  string a, b, q [$];\n"
                 "  K k = new;\n"
                 "  initial begin\n"
                 "    q.push_back(\"x\");\n"
                 "    p::ps.itoa(12); k.ks.itoa(-7); q[0].itoa(0);\n"
                 "    a.itoa(-5); b.itoa(64'h1_0000_0005);\n"
                 "    $display(\"%s %s %s %s %s\", p::ps, k.ks, q[0], a,\n"
                 "             b);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "12 -7 0 -5 5\n");
}

TEST(StringItoaSim, DISABLED_EachToaMethodWritesAStructureMemberString) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { string s; int n; } st_t;\n"
                       "module t;\n"
                       "  st_t a, b, c, d, e;\n"
                       "  initial begin\n"
                       "    a.s.itoa(12); b.s.hextoa(255); c.s.octtoa(8);\n"
                       "    d.s.bintoa(5); e.s.realtoa(2.5);\n"
                       "    $display(\"%s %s %s %s %s\", a.s, b.s, c.s, d.s,\n"
                       "             e.s);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "12 ff 10 101 2.5\n");
}

}  // namespace
