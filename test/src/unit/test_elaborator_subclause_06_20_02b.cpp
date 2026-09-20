#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_param_value.h"
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

}  // namespace
