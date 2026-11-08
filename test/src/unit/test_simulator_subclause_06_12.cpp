#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_real.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(RealDataType, ShortrealHasSinglePrecision) {
  auto v = RunAndGet(
      "module t;\n"
      "  shortreal s;\n"
      "  real rs, rr;\n"
      "  logic differs;\n"
      "  initial begin\n"
      "    s = 0.1;\n"
      "    rs = s;\n"
      "    rr = 0.1;\n"
      "    differs = (rs != rr);\n"
      "  end\n"
      "endmodule\n",
      "differs");
  EXPECT_EQ(v, 1u);
}

TEST(RealDataType, ShortrealDisplaysItsStoredValue) {
  SimFixture f;
  std::string printed = RunCapture(
      "module t;\n"
      "  shortreal s;\n"
      "  string out;\n"
      "  initial begin\n"
      "    s = 0.1;\n"
      "    $sformat(out, \"%f\", s);\n"
      "    $display(\"%s\", out);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed, "0.100000\n");
}

struct ShortrealSource {
  const char* where;
  const char* before;
  const char* decls;
  const char* setup;
  const char* value;
};

std::string ReadShortrealBackAsReal(const ShortrealSource& source) {
  return std::string(source.before) + "module t;\n" + source.decls +
         "  real w;\n  bit [63:0] b;\n  initial begin\n" + source.setup +
         "    w = " + source.value + ";\n    b = $realtobits(w);\n" +
         "  end\nendmodule\n";
}

TEST(RealDataType, ShortrealHoldsTheNearestBinary32InEveryPlaceItIsGiven) {
  const ShortrealSource kSources[] = {
      {"blocking assignment", "", "  shortreal s;\n", "    s = 0.1;\n", "s"},
      {"nonblocking assignment", "", "  shortreal s;\n",
       "    s <= 0.1;\n    #1;\n", "s"},
      {"declaration initializer", "", "  shortreal s = 0.1;\n", "", "s"},
      {"assignment from a real variable", "",
       "  real r = 0.1;\n  shortreal s;\n", "    s = r;\n", "s"},
      {"continuous assignment", "",
       "  real r = 0.1;\n  shortreal s;\n  assign s = r;\n", "    #1;\n", "s"},
      {"cast", "", "", "", "shortreal'(0.1)"},
      {"parameter", "", "  parameter shortreal P = 0.1;\n", "", "P"},
      {"function argument", "",
       "  function automatic real f(shortreal x);\n    return x;\n"
       "  endfunction\n",
       "", "f(0.1)"},
      {"function return value", "",
       "  function automatic shortreal g();\n    return 0.1;\n"
       "  endfunction\n",
       "", "g()"},
      {"task output argument", "",
       "  shortreal s;\n  task automatic k(output shortreal x);\n"
       "    x = 0.1;\n  endtask\n",
       "    k(s);\n", "s"},
      {"input port",
       "module c(input var shortreal x, output real y);\n  assign y = x;\n"
       "endmodule\n",
       "  real r = 0.1;\n  real y;\n  c u(r, y);\n", "    #1;\n", "y"},
  };
  for (const ShortrealSource& source : kSources) {
    SCOPED_TRACE(source.where);
    EXPECT_EQ(RunAndGet(ReadShortrealBackAsReal(source), "b"),
              0x3FB99999A0000000u);
  }
}

TEST(RealDataType, ShortrealRoundsTiesSubnormalsAndOverflowLikeBinary32) {
  struct Rounding {
    ShortrealSource source;
    uint64_t widened;
  };
  const Rounding kRoundings[] = {
      {{"integer halfway between two binary32 values", "",
        "  int i = 16777219;\n  shortreal s;\n", "    s = i;\n", "s"},
       0x4170000040000000u},
      {{"value in the subnormal range", "", "  shortreal s;\n",
        "    s = 1e-45;\n", "s"},
       0x36A0000000000000u},
      {{"value beyond the largest finite binary32", "", "  shortreal s;\n",
        "    s = 1e39;\n", "s"},
       0x7FF0000000000000u},
      {{"negative value beyond the largest finite binary32", "",
        "  shortreal s;\n", "    s = -1e39;\n", "s"},
       0xFFF0000000000000u},
  };
  for (const Rounding& rounding : kRoundings) {
    SCOPED_TRACE(rounding.source.where);
    EXPECT_EQ(RunAndGet(ReadShortrealBackAsReal(rounding.source), "b"),
              rounding.widened);
  }
}

TEST(RealDataType, RealKeepsDoublePrecision) {
  auto v = RunAndGet(
      "module t;\n"
      "  real r1, r2;\n"
      "  logic differs;\n"
      "  initial begin\n"
      "    r1 = 0.1;\n"
      "    r2 = 0.1;\n"
      "    differs = (r1 != r2);\n"
      "  end\n"
      "endmodule\n",
      "differs");
  EXPECT_EQ(v, 0u);
}

TEST(RealDataType, RealFormalsOfAnAutomaticSubroutineCarryTheActual) {
  SimFixture f;
  std::string printed = RunCapture(
      "module t;\n"
      "  int a = 7;\n"
      "  real rr = 5.5;\n"
      "  function automatic real f(real a, real b);\n"
      "    real l;\n"
      "    l = a + b;\n"
      "    return l;\n"
      "  endfunction\n"
      "  task automatic add1(ref real x);\n"
      "    x = x + 1.0;\n"
      "  endtask\n"
      "  initial begin\n"
      "    add1(rr);\n"
      "    $display(\"f=%f ref=%f\", f(2.25, 3.25), rr);\n"
      "    a = 3;\n"
      "    $display(\"a=%0d\", a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed, "f=5.500000 ref=6.500000\na=3\n");
}

TEST(RealDataType, RealFormalIsACopyAndARealReturnConvertsAnInteger) {
  SimFixture f;
  std::string printed = RunCapture(
      "module t;\n"
      "  real r = 1.25;\n"
      "  function automatic real h(real a);\n"
      "    int i;\n"
      "    i = a;\n"
      "    return i;\n"
      "  endfunction\n"
      "  function automatic real dbl(real v);\n"
      "    v = v * 2.0;\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial $display(\"h=%f dbl=%f r=%f\", h(2.5), dbl(r), r);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed, "h=3.000000 dbl=2.500000 r=1.250000\n");
}

TEST(RealDataType, RealPropertyReadInAMethodIsTheObjectsNotTheModules) {
  SimFixture f;
  std::string printed = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    real r;\n"
      "    function real dbl(); return r * 2.0; endfunction\n"
      "    function void bump(); r = r + 0.5; endfunction\n"
      "  endclass\n"
      "  class D;\n"
      "    real r = 1.5;\n"
      "    function real dbl(); return r * 2.0; endfunction\n"
      "  endclass\n"
      "  real r = 2.5;\n"
      "  C h;\n"
      "  D d;\n"
      "  initial begin\n"
      "    h = new; h.r = 3.625;\n"
      "    d = new;\n"
      "    $display(\"prop=%f init=%f\", h.dbl(), d.dbl());\n"
      "    h.bump();\n"
      "    $display(\"h.r=%f r=%f\", h.r, r);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed, "prop=7.250000 init=3.000000\nh.r=4.125000 r=2.500000\n");
}

TEST(RealDataType, RealVarStorage) {
  RealFixture f;
  f.CreateRealVar("x", 1.5);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_NEAR(VecToDouble(var->value), 1.5, 1e-10);
}

TEST(RealDataType, IsRealVariable) {
  RealFixture f;
  f.CreateRealVar("r", 0.0);
  EXPECT_TRUE(f.ctx.IsRealVariable("r"));
  f.ctx.CreateVariable("i", 32);
  EXPECT_FALSE(f.ctx.IsRealVariable("i"));
}

}  // namespace
