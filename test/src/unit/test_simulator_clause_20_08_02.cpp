// §20.8.2 Real math functions — the twenty-one system functions of Table 20-4
// ($ln, $log10, $exp, $sqrt, $pow, $floor, $ceil, $sin, $cos, $tan, $asin,
// $acos, $atan, $atan2, $hypot, $sinh, $cosh, $tanh, $asinh, $acosh, $atanh)
// shall accept real value arguments, return a `real` result, and behave exactly
// like the equivalent C standard-library function named in the table.
//
// The rule's behavior depends on how its argument is produced: a real value can
// come from a real literal, a real variable, or a real constant such as a
// `localparam real` (the §11.2.1 constant form this pass depends on). These
// tests therefore build the argument from real source and drive each module
// through the full pipeline (parse → elaborate → lower → run), reading back
// what the function prints rather than hand-building a call node or stubbing
// the argument. A real result is displayed with %g, whose fractional rendering
// makes both the value and its real-ness directly observable, and %g maps
// straight to the C library's own formatting so a printed value that matches
// the C function is exactly the "matches C" requirement.
#include <sstream>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Runs a single-module source through elaboration and simulation while
// capturing everything the run writes to stdout.
std::string RunCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) {
    LowerAndRun(design, f);
  }
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// Wraps a single %g display of `call` in a module and returns what it prints.
std::string DisplayReal(const std::string& call, SimFixture& f) {
  return RunCapture(
      "module t;\n"
      "  initial $display(\"%g\", " +
          call +
          ");\n"
          "endmodule\n",
      f);
}

// ---------------------------------------------------------------------------
// §20.8.2 (Table 20-4, C1/C2): each function returns the value its C-library
// counterpart would. Arguments are written as real literals so the
// real-argument acceptance of C1 is exercised on every entry.

TEST(RealMath, LnMatchesC) {  // $ln ≡ log
  SimFixture f;
  EXPECT_EQ(DisplayReal("$ln(1.0)", f), "0\n");
}

TEST(RealMath, Log10MatchesC) {  // $log10 ≡ log10
  SimFixture f;
  EXPECT_EQ(DisplayReal("$log10(1000.0)", f), "3\n");
}

TEST(RealMath, ExpMatchesC) {  // $exp ≡ exp; e to six significant figures
  SimFixture f;
  EXPECT_EQ(DisplayReal("$exp(1.0)", f), "2.71828\n");
}

TEST(RealMath, SqrtMatchesC) {  // $sqrt ≡ sqrt
  SimFixture f;
  EXPECT_EQ(DisplayReal("$sqrt(2.25)", f), "1.5\n");
}

TEST(RealMath, PowMatchesC) {  // $pow ≡ pow; two-argument form
  SimFixture f;
  EXPECT_EQ(DisplayReal("$pow(2.0, 10.0)", f), "1024\n");
}

TEST(RealMath, FloorMatchesC) {  // $floor ≡ floor
  SimFixture f;
  EXPECT_EQ(DisplayReal("$floor(7.9)", f), "7\n");
}

TEST(RealMath, CeilMatchesC) {  // $ceil ≡ ceil
  SimFixture f;
  EXPECT_EQ(DisplayReal("$ceil(7.1)", f), "8\n");
}

TEST(RealMath, SinMatchesC) {  // $sin ≡ sin; sin(1) to six significant figures
  SimFixture f;
  EXPECT_EQ(DisplayReal("$sin(1.0)", f), "0.841471\n");
}

TEST(RealMath, CosMatchesC) {  // $cos ≡ cos
  SimFixture f;
  EXPECT_EQ(DisplayReal("$cos(0.0)", f), "1\n");
}

TEST(RealMath, TanMatchesC) {  // $tan ≡ tan
  SimFixture f;
  EXPECT_EQ(DisplayReal("$tan(0.0)", f), "0\n");
}

TEST(RealMath, AsinMatchesC) {  // $asin ≡ asin
  SimFixture f;
  EXPECT_EQ(DisplayReal("$asin(1.0)", f), "1.5708\n");
}

TEST(RealMath, AcosMatchesC) {  // $acos ≡ acos
  SimFixture f;
  EXPECT_EQ(DisplayReal("$acos(1.0)", f), "0\n");
}

TEST(RealMath, AtanMatchesC) {  // $atan ≡ atan
  SimFixture f;
  EXPECT_EQ(DisplayReal("$atan(0.0)", f), "0\n");
}

TEST(RealMath, Atan2MatchesC) {  // $atan2 ≡ atan2; two-argument form
  SimFixture f;
  EXPECT_EQ(DisplayReal("$atan2(0.0, 1.0)", f), "0\n");
}

TEST(RealMath, HypotMatchesC) {  // $hypot ≡ hypot; two-argument form
  SimFixture f;
  EXPECT_EQ(DisplayReal("$hypot(3.0, 4.0)", f), "5\n");
}

TEST(RealMath, SinhMatchesC) {  // $sinh ≡ sinh
  SimFixture f;
  EXPECT_EQ(DisplayReal("$sinh(0.0)", f), "0\n");
}

TEST(RealMath, CoshMatchesC) {  // $cosh ≡ cosh
  SimFixture f;
  EXPECT_EQ(DisplayReal("$cosh(0.0)", f), "1\n");
}

TEST(RealMath,
     TanhMatchesC) {  // $tanh ≡ tanh; tanh(0.5) to six significant figs
  SimFixture f;
  EXPECT_EQ(DisplayReal("$tanh(0.5)", f), "0.462117\n");
}

TEST(RealMath, AsinhMatchesC) {  // $asinh ≡ asinh
  SimFixture f;
  EXPECT_EQ(DisplayReal("$asinh(0.0)", f), "0\n");
}

TEST(RealMath, AcoshMatchesC) {  // $acosh ≡ acosh
  SimFixture f;
  EXPECT_EQ(DisplayReal("$acosh(1.0)", f), "0\n");
}

TEST(RealMath, AtanhMatchesC) {  // $atanh ≡ atanh; atanh(0.5) to six sig figs
  SimFixture f;
  EXPECT_EQ(DisplayReal("$atanh(0.5)", f), "0.549306\n");
}

// ---------------------------------------------------------------------------
// §20.8.2 (C1): "shall accept real value arguments." The C-match tests above
// all pass a real literal, so literal acceptance is already covered; this
// exercises the other production path — a real argument produced by a real
// variable declaration — whose fractional result confirms the value is carried
// as a real, not truncated. (Using a real math function inside a constant
// expression — e.g. a `localparam real` initializer — is a §20.8/§11.2.1
// concern folded at elaboration, a different pipeline stage, so it is not
// exercised here.)

TEST(RealMath, AcceptsRealVariableArgument) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  real r = 2.25;\n"
      "  initial $display(\"%g\", $sqrt(r));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1.5\n");
}

// §20.8.2 (C1): "return a `real` result type." %g renders the payload as a
// double regardless of type, so it cannot distinguish a real result from an
// integral one — but %d can: a real-typed value takes the truncate-to-integer
// path ($pow(2,10) == 1024.0 -> "1024"), whereas an integral value would render
// the raw 64-bit double bit pattern as a huge decimal. A clean "1024" therefore
// observes that the result carries the real result type, not just the value.
TEST(RealMath, ReturnsRealResultType) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"%d\", $pow(2.0, 10.0));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1024\n");
}

// ---------------------------------------------------------------------------
// §20.8.2 (C2): "behavior shall match the equivalent C function" extends to the
// C function's out-of-domain and singular behavior, since %g renders exactly
// what the C library returns.

TEST(RealMath, SqrtOfNegativeMatchesCNaN) {
  SimFixture f;
  // std::sqrt(-1.0) is NaN, printed by %g as "nan".
  EXPECT_EQ(DisplayReal("$sqrt(-1.0)", f), "nan\n");
}

TEST(RealMath, LnOfZeroMatchesCNegativeInfinity) {
  SimFixture f;
  // std::log(0.0) is the pole value -infinity, printed by %g as "-inf".
  EXPECT_EQ(DisplayReal("$ln(0.0)", f), "-inf\n");
}

}  // namespace
