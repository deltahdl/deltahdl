#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(StringMethods, OcttoaStoresOctalText) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.octtoa(8);\n"
      "    n = (s == \"10\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, OcttoaZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.octtoa(0);\n"
      "    n = (s == \"0\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, OcttoaReplacesLongerExisting) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"7777\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.octtoa(7);\n"
      "    n = (s == \"7\") && (s.len() == 1);\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, OcttoaIsInverseOfAtooct) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int r;\n"
      "  initial begin\n"
      "    s.octtoa(511);\n"
      "    r = s.atooct();\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 511u);
}

TEST(StringMethods, OcttoaFromIntegerType) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  integer x = 64;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.octtoa(x);\n"
      "    n = (s == \"100\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, OcttoaFromParameter) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter int P = 8;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.octtoa(P);\n"
      "    n = (s == \"10\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, OcttoaFromLocalparam) {
  auto v = RunAndGet(
      "module t;\n"
      "  localparam int L = 'o777;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.octtoa(L);\n"
      "    n = (s == \"777\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, OcttoaFromExpressionArgument) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int x = 'o70;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.octtoa(x + 'o10);\n"
      "    n = (s == \"100\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, OcttoaResultUsedInConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.octtoa('o17);\n"
      "    u = {s, \"0\"};\n"
      "    n = (u == \"170\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringOcttoaSim, OcttoaWritesNegativeAndWideValuesAsIntegers) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p; string ps; endpackage\n"
                       "module t;\n"
                       "  string a, b;\n"
                       "  initial begin\n"
                       "    a.octtoa(-1); b.octtoa(40'h10_0000_0009);\n"
                       "    p::ps.octtoa(8);\n"
                       "    $display(\"%s %s %s\", a, b, p::ps);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "37777777777 11 10\n");
}

}  // namespace
