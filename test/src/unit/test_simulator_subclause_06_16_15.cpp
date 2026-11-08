#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(StringMethods, RealtoaStoresRealText) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.realtoa(2.5);\n"
      "    n = (s == \"2.5\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, RealtoaZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.realtoa(0.0);\n"
      "    n = (s == \"0\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, RealtoaNegativeValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.realtoa(-1.5);\n"
      "    n = (s == \"-1.5\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, RealtoaIntegerValuedReal) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.realtoa(42.0);\n"
      "    n = (s == \"42\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, RealtoaReplacesLongerExisting) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s = \"old value\";\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.realtoa(1.0);\n"
      "    n = (s == \"1\") && (s.len() == 1);\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, RealtoaIsInverseOfAtoreal) {
  auto d = RunAndGetReal(
      "module t;\n"
      "  string s;\n"
      "  real r;\n"
      "  initial begin\n"
      "    s.realtoa(2.5);\n"
      "    r = s.atoreal();\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_NEAR(d, 2.5, 0.0001);
}

TEST(StringMethods, RealtoaFromRealVariable) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  real x = 3.5;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.realtoa(x);\n"
      "    n = (s == \"3.5\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, RealtoaFromExpressionArgument) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  real x = 1.5;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.realtoa(x + 1.0);\n"
      "    n = (s == \"2.5\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

TEST(StringMethods, RealtoaResultUsedInConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s;\n"
      "  string u;\n"
      "  int n;\n"
      "  initial begin\n"
      "    s.realtoa(2.5);\n"
      "    u = {s, \"V\"};\n"
      "    n = (u == \"2.5V\");\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(v, 1u);
}

}  // namespace
