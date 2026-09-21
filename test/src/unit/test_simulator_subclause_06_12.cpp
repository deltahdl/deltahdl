#include <gtest/gtest.h>

#include <string>

#include "fixture_real.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §6.12: shortreal is the same as a C float, while real is the same as a C
// double. The distinguishing consequence is precision: a value assigned to a
// shortreal is rounded to single precision, so widening it back to a real no
// longer equals the original double-precision literal. 0.1 has no exact binary
// representation, so float(0.1) != double(0.1). Driven through the full
// pipeline so the shortreal declaration (32-bit real storage) and the
// real<-shortreal widening are the production conversion path, not a stub.
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

// §6.12: "The shortreal data type is the same as a C float", and footnote 19
// on the same page: "The real and shortreal types are represented as described
// by IEEE Std 754". A shortreal therefore holds a 32-bit single-precision
// pattern, and every reader of that storage has to decode it as a float. This
// case reads the value back out through a format specification, which is the
// decode path a user reaches with $display, $write and $sformat, and which is
// distinct from the real<-shortreal widening.
//
// Nothing above it covers that path. ShortrealHasSinglePrecision reads through
// `rs = s`, the one decode that is already width-aware, so it passes whatever
// the formatter does. VariableDeclaration.ShortrealDefaultIsZero in
// test/src/unit/test_simulator_subclause_06_08.cpp asserts on the value 0,
// whose float pattern and double pattern are both an all-zero word, so it holds
// under either decoding and can never fail on this.
//
// float(0.1) rendered with %f's default six fractional digits is 0.100000.
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

// §6.12: real is the same as a C double, so a value carried through a real
// keeps full double precision and stays equal to the same double-precision
// literal. This is the accepting counterpart to ShortrealHasSinglePrecision.
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

// §6.12 (printed page 110): real is a C double, and §13.5.1 (printed 348)
// passes an argument by copying it into the subroutine's area, §13.5.2 by a
// reference to the original, so a `real` input formal carries the actual's
// value inside the body and a `ref real` one is the caller's variable. The
// actuals are the issue's: f(2.25, 3.25) through a `real l` local reads 5.5,
// and add1 on `real rr = 5.5` leaves 6.5. Both read 0.0 while the formal and
// the local were known to be real by the value alone and the store into `l`
// or `x` converted the sum as into an integer, whose bits the caller then read
// as a double. The module's `int a` shares the first formal's name: it is
// written after the call, and reads 3 only while the formal's kind stayed on
// the formal rather than on every variable of the name.
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

// §13.5.1 (printed page 348): an input formal is the subroutine's own copy,
// so `v = v * 2.0` inside dbl leaves the caller's r at 1.25 while the call
// returns 2.5; and §13.4.1 with §6.12.1 (printed 110): the implicit variable
// a `real` function returns through has the function's type, so `return i`
// of an int local converts the integer into a real -- 3.0 for the 3 that
// `i = a` rounded 2.5 to -- rather than handing out its bits.
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

// §8.5 (printed page 183): a class property has any data type, so `real r;`
// holds a real, and §8.6 makes the object's properties available to its
// methods, so `r * 2.0` in dbl is real arithmetic on the object's r and reads
// 7.25 for the 3.625 written through the handle. The module declares its own
// `real r = 2.5` beside the class, as the issue's probe does: the method read
// 5.0, twice the module's r, while a bare name in a method was looked up
// among the variables before the class scope (§23.9 with §8.13 puts the class
// first). A property written inside a method, `r = r + 0.5`, reads back
// through the handle as 4.125, the module's r still 2.5, and a real property
// with a declaration initializer doubles to 3.0.
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
