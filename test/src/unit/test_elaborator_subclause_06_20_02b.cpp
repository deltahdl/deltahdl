#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_param_value.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

// §6.20.2 (printed page 126): a parameter with a range specification has the
// range of its declaration, and §7.4.1 (printed 153) makes a packed array of
// two dimensions as many bits as the two ranges multiply to, so `logic
// [HI:1][3:0] V` under `localparam int HI = 8` is 32 bits. The declared type
// was sized without the earlier parameters in scope, which left HI unfolded
// and the width at the vector atom's one bit, and 8ecbbc294 read the span of
// the first range's recorded bounds over that, 8, so `$bits(V)` answered 8
// and a read of V was cut to its low byte, 0xEF. Sized with the parameters
// in scope, $bits(V) is 32 and V reads whole.
TEST(DeclaredWidth, SecondPackedDimensionUnderAParameterBoundMultiplies) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int HI = 8;\n"
      "  localparam logic [HI:1][3:0] V = 32'hDEAD_BEEF;\n"
      "  localparam int BV = $bits(V);\n"
      "  localparam int VR = V;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "BV"), 32);
  EXPECT_EQ(ParamValue(design, "VR"), 0xDEADBEEF);
  const auto* v = FindParam(design, "m", "V");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->decl_width, 32u);
}

// The single range written in terms of the earlier parameter, `logic
// [HI-1:0] W`, is eight bits from the declaration itself now rather than
// from the bounds recorded beside it: W reads 255 through another parameter
// and $bits(W) answers 8, and decl_width, which ConvertOverrideValue in
// src/elaborator/elaborator_module.cpp cuts an override to, holds the 8.
TEST(DeclaredWidth, RangeBoundWrittenAsAParameterFoldsIntoDeclWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int HI = 8;\n"
      "  localparam logic [HI-1:0] W = 8'hFF;\n"
      "  localparam int BW = $bits(W);\n"
      "  localparam int WR = W;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "BW"), 8);
  EXPECT_EQ(ParamValue(design, "WR"), 255);
  const auto* w = FindParam(design, "m", "W");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->decl_width, 8u);
}

// §6.20.2 with §6.18 (printed page 118): a parameter declared with a typedef
// name is of the type the name stands for, and that type's own range may be
// written in terms of an earlier parameter. The declared type was sized
// without the scope's typedefs, which gave a named type no width at all, so
// `$bits(T)` over `typedef logic [HI:1] vec_t; localparam vec_t T` folded to
// nothing; sized with them and HI in scope it is 8, and T reads 0xA5.
TEST(DeclaredWidth, TypedefNamedTypeUnderAParameterBoundIsSized) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int HI = 8;\n"
      "  typedef logic [HI:1] vec_t;\n"
      "  localparam vec_t T = 8'hA5;\n"
      "  localparam int BT = $bits(T);\n"
      "  localparam int TR = T;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "BT"), 8);
  EXPECT_EQ(ParamValue(design, "TR"), 0xA5);
}

// §6.20.2 (printed page 126) with §23.10.1 (printed 765): a defparam's value
// is converted to the range of the parameter it names, `logic [TOP:0] P`
// under `parameter int TOP = 15` being 16 bits, so `defparam u.P = 16'hABCD`
// gives P every bit of the literal and Q, made over after it, reads 0xABCD.
// ConvertOverrideValue cut the value to decl_width, which the body
// declaration's fold without TOP in scope left at 1, so P became 1 and Q
// with it.
TEST(DeclaredWidth, DefparamValueIsCutToTheRangeWrittenAsAParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c;\n"
      "  parameter int TOP = 15;\n"
      "  parameter logic [TOP:0] P = 0;\n"
      "  localparam int Q = P;\n"
      "endmodule\n"
      "module t;\n"
      "  c u();\n"
      "  defparam u.P = 16'hABCD;\n"
      "endmodule\n",
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* q = FindParam(design, "c", "Q");
  ASSERT_NE(q, nullptr);
  EXPECT_TRUE(q->is_resolved);
  EXPECT_EQ(q->resolved_value, 0xABCD);
}

// §6.20.2 (printed page 126) gives a parameter declared `real` a real value,
// and §8.25 declares `real D = 1.5` in a class parameter port list in its own
// example. Each case fails on a registration that folds a class value
// parameter as an integer alone and reports the value when that fold fails,
// which is what rejected every real default and every real override.
TEST(ValueParameters, RealClassParamDefaultIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class Mem #(int size = 4, real D = 1.5);\n"
             "endclass\n"
             "module t;\n"
             "  Mem m;\n"
             "endmodule\n"));
}

TEST(ValueParameters, RealClassParamDefaultOfAModuleScopedClassIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  class Mem #(int size = 4, real D = 1.5);\n"
             "  endclass\n"
             "  Mem m;\n"
             "endmodule\n"));
}

// §6.20.2's first rule: a parameter declared with neither type nor range takes
// the type of its final value, and "if the expression is real, the parameter
// is real".
TEST(ValueParameters, UntypedClassParamWithARealDefaultIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class C #(D = 1.5);\n"
             "endclass\n"
             "module t;\n"
             "  C c;\n"
             "endmodule\n"));
}

// §23.10.2 makes an override a constant expression, which 2.25 is, and §8.25
// applies that rule to a specialization of a class whether it is written in a
// declaration or in an extends clause.
TEST(ValueParameters, RealClassParamOverrideInADeclarationIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class Mem #(real D = 1.5);\n"
             "endclass\n"
             "module t;\n"
             "  Mem #(.D(2.25)) o;\n"
             "endmodule\n"));
}

TEST(ValueParameters, RealClassParamOverrideInAnExtendsClauseIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class Mem #(real D = 1.5);\n"
             "endclass\n"
             "module t;\n"
             "  class E extends Mem #(2.25);\n"
             "  endclass\n"
             "endmodule\n"));
}

// A real default is still a constant_param_expression, so one that reads a
// variable is reported as an integer one is. This fails on a repair that
// accepts every default of a real parameter. The `r` stands on line 3.
TEST(ValueParameters, NonConstantRealClassParamDefaultIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  class C #(real D = r);\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "class parameter 'D' value is not a constant expression", 3, "6.20.2"));
}

// §6.20.2's real parameter is a constant as an integral one is, so it is a
// legal override in an extends clause. That clause's check folds the module's
// parameters as integers, and read the real `R` as a name it could not fold.
TEST(ValueParameters, RealModuleParamAsAnExtendsOverrideIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class Mem #(real D = 1.5);\n"
             "endclass\n"
             "module t;\n"
             "  parameter real R = 2.5;\n"
             "  class E extends Mem #(R);\n"
             "  endclass\n"
             "endmodule\n"));
}

}  // namespace
