#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <string>
#include <string_view>

#include "fixture_real.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(RealConversion, CastRealToIntNegativeTieRoundsAway) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  real r;\n"
      "  int result;\n"
      "  initial begin\n"
      "    r = -1.5;\n"
      "    result = int'(r);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  auto neg2_32bit = static_cast<uint32_t>(-2);
  EXPECT_EQ(var->value.ToUint64(), neg2_32bit);
}

TEST(RealConversion, CastRealToIntRoundsToNearestTiesAway) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r1, r2, r3;\n"
      "  int a, b, c;\n"
      "  initial begin\n"
      "    r1 = 35.7; a = int'(r1);\n"
      "    r2 = 35.5; b = int'(r2);\n"
      "    r3 = 35.2; c = int'(r3);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 36u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 36u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 35u);
}

TEST(RealConversion, ImplicitRealToIntRoundsToNearest) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  real r;\n"
      "  int result;\n"
      "  initial begin\n"
      "    r = 1.5;\n"
      "    result = r;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(RealConversion, ImplicitIntToReal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int i;\n"
      "  real r;\n"
      "  initial begin\n"
      "    i = 42;\n"
      "    r = i;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_NEAR(VecToDouble(var->value), 42.0, 1e-10);
}

TEST(RealConversion, KnownBitsSurviveWhileXBitsZeroOnRealConversion) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] val;\n"
      "  real r;\n"
      "  initial begin\n"
      "    val = 8'b1010xxxx;\n"
      "    r = val;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_NEAR(VecToDouble(var->value), 160.0, 1e-10);
}

TEST(RealConversion, HighZBitsBecomeZeroOnRealConversion) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] val;\n"
      "  real r;\n"
      "  initial begin\n"
      "    val = 8'b1010zzzz;\n"
      "    r = val;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_NEAR(VecToDouble(var->value), 160.0, 1e-10);
}

TEST(RealConversion, ImplicitNegativeNonTieRoundsToNearest) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r1, r2;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    r1 = -2.7; a = r1;\n"
      "    r2 = -2.2; b = r2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(),
            static_cast<uint32_t>(-3));
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(),
            static_cast<uint32_t>(-2));
}

TEST(RealConversion, DeclInitRealToIntRoundsNotTruncates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int i = 35.7;\n"
      "endmodule\n",
      f, "i");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 36u);
}

TEST(RealConversion, DeclInitRealToIntTiesAwayFromZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a = 35.5;\n"
      "  int b = 1.5;\n"
      "  int c = -1.5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 36u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(),
            static_cast<uint32_t>(-2));
}

TEST(RealConversion, IntegerConvertsToRealByItsSignedOrUnsignedValue) {
  struct Place {
    const char* where;
    const char* decls;
    const char* setup;
    uint64_t widened;
  };
  const Place kPlaces[] = {
      {"int assigned to a real", "  int n = -3;\n  real s;\n", "    s = n;\n",
       0xC008000000000000u},
      {"real initializer", "  real s = -3;\n", "", 0xC008000000000000u},
      {"byte assigned to a shortreal", "  byte n = -3;\n  shortreal s;\n",
       "    s = n;\n", 0xC008000000000000u},
      {"shortreal initializer", "  shortreal s = -3;\n", "",
       0xC008000000000000u},
      {"longint assigned to a real by nonblocking assignment",
       "  longint n = -3;\n  real s;\n", "    s <= n;\n    #1;\n",
       0xC008000000000000u},
      {"unsigned vector assigned to a real",
       "  bit [7:0] n = 8'hFD;\n  real s;\n", "    s = n;\n",
       0x406FA00000000000u},
  };
  for (const Place& place : kPlaces) {
    SCOPED_TRACE(place.where);
    const std::string kSrc = std::string("module t;\n") + place.decls +
                             "  real w;\n  bit [63:0] b;\n  initial begin\n" +
                             place.setup +
                             "    w = s;\n    b = $realtobits(w);\n"
                             "  end\nendmodule\n";
    EXPECT_EQ(RunAndGet(kSrc, "b"), place.widened);
  }
}

TEST(RealConversion, StructurePatternItemConvertsToItsMembersType) {
  const std::string kSrc =
      "module t;\n"
      "  struct { int k; real r; shortreal s; } st = '{2.5, -3, 0.1};\n"
      "  int k;\n"
      "  bit [63:0] b, c;\n"
      "  initial begin\n"
      "    k = st.k;\n"
      "    b = $realtobits(st.r);\n"
      "    c = $realtobits(real'(st.s));\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "k"), 3u);
  EXPECT_EQ(RunAndGet(kSrc, "b"), 0xC008000000000000u);
  EXPECT_EQ(RunAndGet(kSrc, "c"), 0x3FB99999A0000000u);
}

TEST(RealConversion, DeclInitIntToReal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  real r = 5;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_NEAR(VecToDouble(var->value), 5.0, 1e-10);
}

TEST(RealConversion, DeclInitXzBitsBecomeZeroOnRealConversion) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  real r = 8'b1010xxxx;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_NEAR(VecToDouble(var->value), 160.0, 1e-10);
}

TEST(RealConversion, NonblockingAssignConvertsBothDirections) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  int i;\n"
      "  int j;\n"
      "  real s;\n"
      "  initial begin\n"
      "    r = 2.5;\n"
      "    i <= r;\n"
      "    j = 7;\n"
      "    s <= j;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("i")->value.ToUint64(), 3u);
  EXPECT_NEAR(VecToDouble(f.ctx.FindVariable("s")->value), 7.0, 1e-10);
}

TEST(RealConversion, ShortRealToIntRoundsToNearest) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  shortreal sr;\n"
      "  int i;\n"
      "  initial begin\n"
      "    sr = 2.5;\n"
      "    i = sr;\n"
      "  end\n"
      "endmodule\n",
      f, "i");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(RealConversion, RealtimeToIntRoundsToNearest) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  realtime rt;\n"
      "  int i;\n"
      "  initial begin\n"
      "    rt = 1.5;\n"
      "    i = rt;\n"
      "  end\n"
      "endmodule\n",
      f, "i");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(RealConversion, RealToLongintRoundsToNearest) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  real r;\n"
      "  longint l;\n"
      "  initial begin\n"
      "    r = 35.5;\n"
      "    l = r;\n"
      "  end\n"
      "endmodule\n",
      f, "l");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 36u);
}

TEST(RealConversion, BlockDeclInitIntToReal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  real out;\n"
      "  initial begin\n"
      "    static real r = 5;\n"
      "    out = r;\n"
      "  end\n"
      "endmodule\n",
      f, "out");
  ASSERT_NE(var, nullptr);
  EXPECT_NEAR(VecToDouble(var->value), 5.0, 1e-10);
}

TEST(RealConversion, RealActualRoundsIntoAnIntFormal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  function int fi(input int x); return x; endfunction\n"
      "  int a;\n"
      "  initial a = fi(12.5);\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 13u);
}

TEST(RealConversion, RealVariableActualRoundsIntoAnIntFormal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  function int fi(input int x); return x; endfunction\n"
      "  real r = 12.5;\n"
      "  int a;\n"
      "  initial a = fi(r);\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 13u);
}

TEST(RealConversion, NegativeRealActualRoundsAwayIntoAShortintFormal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  function shortint fs(input shortint x); return x; endfunction\n"
      "  shortint a;\n"
      "  initial a = fs(-3.5);\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFCu);
}

TEST(RealConversion, RealActualRoundsIntoALongintFormal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  function longint fl(input longint x); return x; endfunction\n"
      "  longint a;\n"
      "  initial a = fl(12.5);\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 13u);
}

TEST(RealConversion, NegativeRealActualRoundsAwayIntoAByteFormal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  function byte fb(input byte x); return x; endfunction\n"
      "  byte a;\n"
      "  initial a = fb(-3.5);\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFCu);
}

TEST(RealConversion, RealActualRoundsIntoAConstructorIntFormal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    int r;\n"
      "    function new(input int v); r = v; endfunction\n"
      "  endclass\n"
      "  int a;\n"
      "  initial begin\n"
      "    static C c = new(6.5);\n"
      "    a = c.r;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(RealConversion, RealActualRoundsIntoAClassMethodIntFormal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    function int m(input int x); return x; endfunction\n"
      "  endclass\n"
      "  int a;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    a = c.m(12.5);\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 13u);
}

TEST(RealConversion, StaticPropertyRealInitializerRoundsIntoAnInt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    static int t = 3.6;\n"
      "  endclass\n"
      "  int a;\n"
      "  initial a = C::t;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(RealConversion, StaticPropertyNegativeRealInitializerRoundsAway) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    static int u = -2.5;\n"
      "  endclass\n"
      "  int a;\n"
      "  initial a = C::u;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), static_cast<uint32_t>(-3));
}

TEST(RealConversionSim, AssignmentToAnArrayElementConverts) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  real rv = 2.0;\n"
                       "  logic signed [3:0] s = -1;\n"
                       "  logic [7:0] r [1:2];\n"
                       "  logic [7:0] x;\n"
                       "  real ra [2];\n"
                       "  initial begin\n"
                       "    r[1] = rv + s;\n"
                       "    r[2] = 2.6;\n"
                       "    x = rv + s;\n"
                       "    ra[0] = 3;\n"
                       "    ra[1] = 1.25;\n"
                       "    $display(\"%h %h %h %0.2f %0.2f\", r[1], r[2], x,\n"
                       "             ra[0], ra[1]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "01 03 01 3.00 1.25\n");
}

struct ConversionPlace {
  const char* where;
  const char* before;
  const char* decls;
  const char* stmts;
  const char* result;
};

std::string Substituted(std::string text, std::string_view value) {
  for (size_t at = text.find('@'); at != std::string::npos;
       at = text.find('@', at + value.size())) {
    text.replace(at, 1, value);
  }
  return text;
}

std::string DisplayAfterwards(const ConversionPlace& place,
                              std::string_view format) {
  return std::string(place.before)
      .append("module t;\n")
      .append(place.decls)
      .append("  initial begin\n")
      .append(place.stmts)
      .append("    #1;\n    $display(\"")
      .append(format)
      .append("\", ")
      .append(place.result)
      .append(");\n  end\nendmodule\n");
}

struct Rounding {
  const char* real;
  const char* integer;
};

constexpr Rounding kRoundings[] = {
    {"35.7", "36"}, {"35.5", "36"}, {"35.2", "35"},   {"-1.5", "-2"},
    {"1.5", "2"},   {"2.5", "3"},   {"-2.5", "-3"},   {"-35.2", "-35"},
    {"0.5", "1"},   {"-0.4", "0"},  {"-35.5", "-36"},
};

void ExpectEveryPlaceRounds(std::initializer_list<ConversionPlace> places) {
  for (const ConversionPlace& place : places) {
    for (const Rounding& rounding : kRoundings) {
      SCOPED_TRACE(std::string(place.where).append(" ").append(rounding.real));
      SimFixture f;
      EXPECT_EQ(
          RunCapture(
              Substituted(DisplayAfterwards(place, "%0d"), rounding.real), f),
          std::string(rounding.integer).append("\n"));
    }
  }
}

TEST(RealConversion, ARealRoundsToTheNearestIntegerInEveryPlace) {
  ExpectEveryPlaceRounds({
      {"blocking assignment to an int", "", "  real n = @;\n  int i;\n",
       "    i = n;\n", "i"},
      {"blocking assignment to an integer", "", "  real n = @;\n  integer i;\n",
       "    i = n;\n", "i"},
      {"blocking assignment to a byte", "", "  real n = @;\n  byte i;\n",
       "    i = n;\n", "i"},
      {"blocking assignment to a shortint", "",
       "  real n = @;\n  shortint i;\n", "    i = n;\n", "i"},
      {"blocking assignment to a longint", "", "  real n = @;\n  longint i;\n",
       "    i = n;\n", "i"},
      {"blocking assignment to a signed vector", "",
       "  real n = @;\n  logic signed [7:0] i;\n", "    i = n;\n", "i"},
      {"assignment of a literal", "", "  int i;\n", "    i = @;\n", "i"},
      {"nonblocking assignment", "", "  real n = @;\n  int i;\n",
       "    i <= n;\n", "i"},
      {"declaration initializer", "", "  int i = @;\n", "", "i"},
      {"continuous assignment", "",
       "  real n = @;\n  int i;\n  assign i = n;\n", "", "i"},
      {"shortreal source", "", "  shortreal n = @;\n  int i;\n", "    i = n;\n",
       "i"},
      {"realtime source", "", "  realtime n = @;\n  int i;\n", "    i = n;\n",
       "i"},
      {"real expression", "", "  real n = @;\n  int i;\n", "    i = n * 1.0;\n",
       "i"},
      {"conditional expression", "", "  real n = @;\n  int i;\n",
       "    i = n > 100.0 ? 0.0 : n;\n", "i"},
      {"function return value", "",
       "  real n = @;\n  function int f();\n    return n;\n  endfunction\n", "",
       "f()"},
      {"task output argument", "",
       "  int i;\n  task automatic k(output real x);\n    x = @;\n"
       "  endtask\n",
       "    k(i);\n", "i"},
      {"input port",
       "module c(input var int x, output int y);\n  assign y = x;\n"
       "endmodule\n",
       "  real n = @;\n  int y;\n  c u(n, y);\n", "", "y"},
      {"output port", "module c(output real x);\n  assign x = @;\nendmodule\n",
       "  int y;\n  c u(y);\n", "", "y"},
      {"parameter override",
       "module c #(parameter int P = 0) (output int y);\n  assign y = P;\n"
       "endmodule\n",
       "  int y;\n  c #(.P(@)) u(y);\n", "", "y"},
      {"package variable initializer", "package k;\n  int i = @;\nendpackage\n",
       "", "", "k::i"},
      {"compilation-unit variable initializer", "int i = @;\n", "", "", "i"},
      {"interface variable initializer",
       "interface ifc;\n  int i = @;\nendinterface\n", "  ifc u();\n", "",
       "u.i"},
      {"generate block variable initializer", "",
       "  if (1) begin : g\n    int i = @;\n  end\n", "", "g.i"},
      {"class property", "class C;\n  int p;\nendclass\n",
       "  real n = @;\n  C c = new;\n", "    c.p = n;\n", "c.p"},
      {"static class property initializer",
       "class C;\n  static int p = @;\nendclass\n", "", "", "C::p"},
      {"array element", "", "  real n = @;\n  int a[2];\n", "    a[1] = n;\n",
       "a[1]"},
      {"structure assignment pattern", "",
       "  real n = @;\n  struct { int m; } s;\n", "    s = '{m: n};\n", "s.m"},
  });
}

TEST(RealConversion, DISABLED_ARealWrittenToAMemberRoundsToTheMembersType) {
  ExpectEveryPlaceRounds({
      {"unpacked structure member", "",
       "  real n = @;\n  struct { int m; } s;\n", "    s.m = n;\n", "s.m"},
      {"byte member", "", "  real n = @;\n  struct { int k; byte m; } s;\n",
       "    s.m = n;\n", "s.m"},
      {"member given a literal", "", "  struct { int m; } s;\n",
       "    s.m = @;\n", "s.m"},
      {"member by nonblocking assignment", "",
       "  real n = @;\n  struct { int m; } s;\n", "    s.m <= n;\n", "s.m"},
      {"member by continuous assignment", "",
       "  real n = @;\n  struct { int m; } s;\n  assign s.m = n;\n", "", "s.m"},
      {"packed structure member", "",
       "  real n = @;\n  struct packed { logic signed [7:0] m; } s;\n",
       "    s.m = n;\n", "s.m"},
      {"packed union member", "",
       "  real n = @;\n  union packed { logic signed [7:0] m; } s;\n",
       "    s.m = n;\n", "s.m"},
      {"member of a structure in a class",
       "class C;\n  struct { int m; } s;\nendclass\n",
       "  real n = @;\n  C c = new;\n", "    c.s.m = n;\n", "c.s.m"},
      {"member of a structure in a package",
       "package k;\n  struct { int m; } s;\nendpackage\n", "  real n = @;\n",
       "    k::s.m = n;\n", "k::s.m"},
      {"member of an array element", "",
       "  real n = @;\n  struct { int m; } s[2];\n", "    s[1].m = n;\n",
       "s[1].m"},
  });
}

TEST(RealConversion, XAndZBitsReadAsZeroInEveryPlaceAnIntegerBecomesReal) {
  const ConversionPlace kPlaces[] = {
      {"blocking assignment", "", "  logic [7:0] v = 8'b1010xxzz;\n  real r;\n",
       "    r = v;\n", "r"},
      {"nonblocking assignment", "",
       "  logic [7:0] v = 8'b1010xxzz;\n  real r;\n", "    r <= v;\n", "r"},
      {"shortreal target", "",
       "  logic [7:0] v = 8'b1010xxzz;\n  shortreal r;\n", "    r = v;\n", "r"},
      {"realtime target", "", "  logic [7:0] v = 8'b1010xxzz;\n  realtime r;\n",
       "    r = v;\n", "r"},
      {"continuous assignment", "",
       "  logic [7:0] v = 8'b1010xxzz;\n  real r;\n  assign r = v;\n", "", "r"},
      {"function argument", "",
       "  logic [7:0] v = 8'b1010xxzz;\n"
       "  function automatic real f(real x);\n    return x;\n  endfunction\n",
       "", "f(v)"},
      {"function return value", "",
       "  logic [7:0] v = 8'b1010xxzz;\n"
       "  function automatic real f();\n    return v;\n  endfunction\n",
       "", "f()"},
      {"input port",
       "module c(input var real x, output real y);\n  assign y = x;\n"
       "endmodule\n",
       "  logic [7:0] v = 8'b1010xxzz;\n  real y;\n  c u(v, y);\n", "", "y"},
      {"net driven with x and z", "",
       "  wire [7:0] v = 8'b1010xxzz;\n  real r;\n", "    #1 r = v;\n", "r"},
      {"structure member", "",
       "  logic [7:0] v = 8'b1010xxzz;\n  struct { real m; } s;\n",
       "    s = '{m: v};\n", "s.m"},
  };
  for (const ConversionPlace& place : kPlaces) {
    SCOPED_TRACE(place.where);
    SimFixture f;
    EXPECT_EQ(RunCapture(DisplayAfterwards(place, "%f"), f), "160.000000\n");
  }
}

TEST(RealConversion, AnUnknownSignBitOrUndrivenNetReadsAsZeroOnConversion) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic signed [7:0] sv = 8'bx0000011;\n"
                       "  integer n;\n"
                       "  wire [3:0] w;\n"
                       "  real a, b, c;\n"
                       "  initial begin\n"
                       "    n = 'x;\n"
                       "    n[3:0] = 4'b0101;\n"
                       "    a = sv;\n"
                       "    b = n;\n"
                       "    c = w;\n"
                       "    $display(\"%f %f %f\", a, b, c);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3.000000 5.000000 0.000000\n");
}

}  // namespace
