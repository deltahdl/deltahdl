#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(StringMethods, BintoaStoresBinaryText) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.bintoa(10);\n"
      "    n = (s == \"1010\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, BintoaZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.bintoa(0);\n"
      "    n = (s == \"0\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, BintoaReplacesLongerExisting) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"1111\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.bintoa(1);\n"
      "    n = (s == \"1\") && (s.len() == 1);\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, BintoaIsInverseOfAtobin) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int r;\n"
      "  initial begin\n"
      "    s.bintoa(13);\n"
      "    r = s.atobin();\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 13u);
}

TEST(StringMethods, BintoaFromIntegerType) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  integer x = 6;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.bintoa(x);\n"
      "    n = (s == \"110\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, BintoaFromParameter) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter int P = 5;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.bintoa(P);\n"
      "    n = (s == \"101\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, BintoaFromLocalparam) {
  auto v = RunAndGet(
      "module t;\n"
      "  localparam int L = 'b1011;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.bintoa(L);\n"
      "    n = (s == \"1011\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, BintoaFromExpressionArgument) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int x = 'b1010;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.bintoa(x + 'b0001);\n"
      "    n = (s == \"1011\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, BintoaResultUsedInConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.bintoa('b11);\n"
      "    u = {s, \"0\"};\n"
      "    n = (u == \"110\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringBintoaSim, BintoaWritesNegativeAndWideValuesAsIntegers) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  string a, b, q [$];\n"
                       "  initial begin\n"
                       "    q.push_back(\"\");\n"
                       "    a.bintoa(-2); b.bintoa(36'h8_0000_0003);\n"
                       "    q[0].bintoa(5);\n"
                       "    $display(\"%s %s %s\", a, b, q[0]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "11111111111111111111111111111110 11 101\n");
}

}  // namespace
