#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(StringMethods, HextoaStoresHexText) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.hextoa(255);\n"
      "    n = (s == \"ff\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, HextoaZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.hextoa(0);\n"
      "    n = (s == \"0\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, HextoaReplacesLongerExisting) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"ffffff\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.hextoa(7);\n"
      "    n = (s == \"7\") && (s.len() == 1);\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, HextoaIsInverseOfAtohex) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int r;\n"
      "  initial begin\n"
      "    s.hextoa('hABC);\n"
      "    r = s.atohex();\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0xABCu);
}

TEST(StringMethods, HextoaFromIntegerType) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  integer x = 'hBEE;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.hextoa(x);\n"
      "    n = (s == \"bee\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, HextoaFromParameter) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter int P = 'hFF;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.hextoa(P);\n"
      "    n = (s == \"ff\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, HextoaFromLocalparam) {
  auto v = RunAndGet(
      "module t;\n"
      "  localparam int L = 'h500;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.hextoa(L);\n"
      "    n = (s == \"500\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, HextoaFromExpressionArgument) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int x = 'hF0;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.hextoa(x + 'hF);\n"
      "    n = (s == \"ff\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, HextoaResultUsedInConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.hextoa('h1f);\n"
      "    u = {s, \"0\"};\n"
      "    n = (u == \"1f0\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, HextoaConvertsItsArgumentToInteger) {
  auto v = RunAndGet(
      "module t;\n"
      "  string h;\n"
      "  longint w = 64'h1_0000_0005;\n"
      "  int n;\n"
      "  initial begin h.hextoa(w); n = (h == \"5\"); end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringHextoaSim, HextoaWritesNegativeAndWideValuesAsIntegers) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class K; string ks = \"old\"; endclass\n"
                       "module t;\n"
                       "  string a, b;\n"
                       "  K k = new;\n"
                       "  initial begin\n"
                       "    a.hextoa(-1); b.hextoa(64'h1_0000_00ab);\n"
                       "    k.ks.hextoa(255);\n"
                       "    $display(\"%s %s %s\", a, b, k.ks);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "ffffffff ab ff\n");
}

}  // namespace
