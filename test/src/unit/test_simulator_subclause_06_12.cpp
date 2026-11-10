#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
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
      {"package variable initializer",
       "package pk;\n  shortreal s = 0.1;\nendpackage\n", "", "", "pk::s"},
      {"compilation-unit variable initializer", "shortreal s = 0.1;\n", "", "",
       "s"},
      {"interface variable initializer",
       "interface ifc;\n  shortreal s = 0.1;\nendinterface\n", "  ifc i();\n",
       "", "i.s"},
      {"program variable initializer",
       "program p(output real y);\n  shortreal s = 0.1;\n  assign y = s;\n"
       "endprogram\n",
       "  real y;\n  p u(y);\n", "    #1;\n", "y"},
      {"generate block variable initializer", "",
       "  if (1) begin : g\n    shortreal s = 0.1;\n  end\n", "", "g.s"},
      {"loop generate block variable initializer", "",
       "  for (genvar i = 0; i < 2; i++) begin : g\n"
       "    shortreal s = 0.1;\n  end\n",
       "", "g[1].s"},
      {"class property initializer",
       "class C;\n  shortreal s = 0.1;\nendclass\n", "  C h = new;\n", "",
       "h.s"},
      {"static class property initializer",
       "class C;\n  static shortreal s = 0.1;\nendclass\n", "", "", "C::s"},
      {"unpacked array element initializer", "",
       "  shortreal a[2] = '{0.1, 0.2};\n", "", "a[0]"},
      {"unpacked structure member initializer", "",
       "  struct { shortreal m; int k; } st = '{0.1, 1};\n", "", "st.m"},
      {"function local initializer", "",
       "  function automatic real f();\n    shortreal x = 0.1;\n"
       "    return x;\n  endfunction\n",
       "", "f()"},
      {"block local initializer", "", "",
       "    begin : blk\n      static shortreal x = 0.1;\n      w = x;\n"
       "    end\n",
       "w"},
      {"block local assignment", "", "",
       "    begin : blk\n      shortreal x;\n      x = 0.1;\n      w = x;\n"
       "    end\n",
       "w"},
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

void ExpectEveryReadBack(std::initializer_list<ShortrealSource> sources,
                         uint64_t bits) {
  for (const ShortrealSource& source : sources) {
    SCOPED_TRACE(source.where);
    EXPECT_EQ(RunAndGet(ReadShortrealBackAsReal(source), "b"), bits);
  }
}

constexpr uint64_t kTenthAsBinary64 = 0x3FB999999999999Au;

TEST(RealDataType, RealAndRealtimeHoldTheNearestBinary64InEveryPlace) {
  ExpectEveryReadBack(
      {
          {"real blocking assignment", "", "  real s;\n", "    s = 0.1;\n",
           "s"},
          {"real nonblocking assignment", "", "  real s;\n",
           "    s <= 0.1;\n    #1;\n", "s"},
          {"real declaration initializer", "", "  real s = 0.1;\n", "", "s"},
          {"realtime declaration initializer", "", "  realtime s = 0.1;\n", "",
           "s"},
          {"realtime assignment from a real", "",
           "  real r = 0.1;\n  realtime s;\n", "    s = r;\n", "s"},
          {"real continuous assignment", "",
           "  realtime r = 0.1;\n  real s;\n  assign s = r;\n", "    #1;\n",
           "s"},
          {"real parameter", "", "  parameter real P = 0.1;\n", "", "P"},
          {"realtime parameter", "", "  parameter realtime P = 0.1;\n", "",
           "P"},
          {"realtime function argument and return value", "",
           "  function automatic realtime f(realtime x);\n    return x;\n"
           "  endfunction\n",
           "", "f(0.1)"},
          {"realtime task output argument", "",
           "  realtime s;\n  task automatic k(output realtime x);\n"
           "    x = 0.1;\n  endtask\n",
           "    k(s);\n", "s"},
          {"realtime input port",
           "module c(input var realtime x, output real y);\n"
           "  assign y = x;\nendmodule\n",
           "  real r = 0.1;\n  real y;\n  c u(r, y);\n", "    #1;\n", "y"},
          {"package realtime initializer",
           "package pk;\n  realtime s = 0.1;\nendpackage\n", "", "", "pk::s"},
          {"compilation-unit real initializer", "real s = 0.1;\n", "", "", "s"},
          {"interface realtime initializer",
           "interface ifc;\n  realtime s = 0.1;\nendinterface\n",
           "  ifc i();\n", "", "i.s"},
          {"generate block real initializer", "",
           "  if (1) begin : g\n    real s = 0.1;\n  end\n", "", "g.s"},
          {"class realtime property initializer",
           "class C;\n  realtime s = 0.1;\nendclass\n", "  C h = new;\n", "",
           "h.s"},
          {"realtime array element initializer", "",
           "  realtime a[2] = '{0.1, 0.2};\n", "", "a[0]"},
          {"realtime structure member initializer", "",
           "  struct { realtime m; int k; } st = '{0.1, 1};\n", "", "st.m"},
          {"block local realtime", "", "",
           "    begin : blk\n      realtime x;\n      x = 0.1;\n      w = x;\n"
           "    end\n",
           "w"},
          {"real typedef of a package, declared in the package",
           "package pk;\n  typedef real R;\n  R s = 0.1;\nendpackage\n", "", "",
           "pk::s"},
          {"real typedef of the compilation unit, declared there",
           "typedef real R;\nR s = 0.1;\n", "", "", "s"},
          {"real typedef, as an array element", "",
           "  typedef real R;\n  R a[2] = '{0.1, 0.2};\n", "", "a[0]"},
          {"real typedef, as a function return type", "",
           "  typedef real R;\n  function automatic R f();\n"
           "    return 0.1;\n  endfunction\n",
           "", "f()"},
      },
      kTenthAsBinary64);
}

TEST(RealDataType, DISABLED_AVariableOfARealTypedefHoldsTheNearestBinary64) {
  ExpectEveryReadBack(
      {
          {"module real typedef initializer", "",
           "  typedef real R;\n  R s = 0.1;\n", "", "s"},
          {"module realtime typedef initializer", "",
           "  typedef realtime T;\n  T s = 0.1;\n", "", "s"},
          {"module real typedef assignment", "", "  typedef real R;\n  R s;\n",
           "    s = 0.1;\n", "s"},
          {"package real typedef, declared in a module",
           "package pk;\n  typedef real R;\nendpackage\n", "  pk::R s = 0.1;\n",
           "", "s"},
          {"compilation-unit real typedef, declared in a module",
           "typedef real R;\n", "  R s = 0.1;\n", "", "s"},
          {"interface real typedef",
           "interface ifc;\n  typedef real R;\n  R s = 0.1;\nendinterface\n",
           "  ifc i();\n", "", "i.s"},
          {"real typedef in a generate block", "",
           "  typedef real R;\n  if (1) begin : g\n    R s = 0.1;\n  end\n", "",
           "g.s"},
          {"structure member of a real typedef", "",
           "  typedef real R;\n  struct { R m; } st = '{m: 0.1};\n", "",
           "st.m"},
          {"task output into a real typedef variable", "",
           "  typedef real R;\n  R s;\n"
           "  task automatic k(output R x);\n    x = 0.1;\n  endtask\n",
           "    k(s);\n", "s"},
          {"block local real typedef", "", "  typedef real R;\n",
           "    begin : blk\n      static R x = 0.1;\n      w = x;\n"
           "    end\n",
           "w"},
      },
      kTenthAsBinary64);
  ExpectEveryReadBack({{"module shortreal typedef initializer", "",
                        "  typedef shortreal S;\n  S s = 0.1;\n", "", "s"}},
                      0x3FB99999A0000000u);
}

TEST(RealDataType, BitsOfARealVariableIsItsBinaryFormatsWidth) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  real r;\n  shortreal s;\n  realtime q;\n"
                       "  typedef real R;\n  typedef shortreal S;\n"
                       "  typedef realtime T;\n"
                       "  initial $display(\"%0d %0d %0d %0d %0d %0d\", "
                       "$bits(r), $bits(s), $bits(q), $bits(R), $bits(S), "
                       "$bits(T));\n"
                       "endmodule\n",
                       f),
            "64 32 64 64 32 64\n");
}

TEST(RealDataType, DISABLED_BitsOfARealTypeKeywordIsItsBinaryFormatsWidth) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  initial $display(\"%0d %0d %0d\", $bits(real), "
                       "$bits(shortreal), $bits(realtime));\n"
                       "endmodule\n",
                       f),
            "64 32 64\n");
}

TEST(RealDataType, DISABLED_RealtimeIsTheSameTypeAsReal) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  real r;\n  realtime q;\n  shortreal s;\n"
                       "  typedef realtime T;\n"
                       "  initial $display(\"%0d %0d %0d %0d %0d\", "
                       "type(realtime) == type(real), type(q) == type(r), "
                       "type(T) == type(real), type(s) == type(realtime), "
                       "type(q) != type(r));\n"
                       "endmodule\n",
                       f),
            "1 1 1 0 0\n");
}

TEST(RealDataType, RealAndRealtimeActualsBindToEachOthersRefFormals) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  real r = 1.0;\n  realtime q = 1.0;\n"
                       "  task automatic a(ref realtime x);\n"
                       "    x += 1.5;\n  endtask\n"
                       "  task automatic b(ref real x);\n"
                       "    x += 2.5;\n  endtask\n"
                       "  initial begin\n    a(r);\n    b(q);\n"
                       "    $display(\"%f %f\", r, q);\n  end\n"
                       "endmodule\n",
                       f),
            "2.500000 3.500000\n");
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
