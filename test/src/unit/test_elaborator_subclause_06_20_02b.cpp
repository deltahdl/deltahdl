#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_param_value.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

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

TEST(ValueParameters, UntypedClassParamWithARealDefaultIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class C #(D = 1.5);\n"
             "endclass\n"
             "module t;\n"
             "  C c;\n"
             "endmodule\n"));
}

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

TEST(TypedParameterSign, PackageParameterOfAnUnsignedTypeReadsUnsigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter bit [3:0] P = 24;\n"
      "endpackage\n"
      "module m;\n"
      "  localparam int Q = p::P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "Q"), 8);
}

TEST(TypedParameterSign, CompilationUnitParameterWithARangeReadsUnsigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "parameter [3:0] R = 24;\n"
      "module m;\n"
      "  localparam int Q = R;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "Q"), 8);
}

TEST(TypedParameterSign, PackageParameterOfASignedTypeReadsSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter byte B = 8'd200;\n"
      "endpackage\n"
      "module m;\n"
      "  localparam int Q = p::B;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "Q"), -56);
}

TEST(TypedParameterSign, ClassParameterOfAnUnsignedTypeReadsUnsigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C #(bit [3:0] P = 24);\n"
      "endclass\n"
      "module m;\n"
      "  localparam int Q = C#()::P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "Q"), 8);
}

TEST(TypedefParameterType, PackageParameterIsCutToTheTypedefWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef bit [3:0] nib;\n"
      "  parameter nib P = 12'hFFF;\n"
      "endpackage\n"
      "module m;\n"
      "  localparam int Q = p::P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "Q"), 15);
}

TEST(TypedefParameterType, CompilationUnitParameterIsCutToTheTypedefWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "typedef bit [3:0] nib;\n"
      "parameter nib R = 12'hFFF;\n"
      "module m;\n"
      "  localparam int Q = R;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "Q"), 15);
}

TEST(TypedefParameterType, ClassParameterIsCutToTheTypedefWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "typedef bit [3:0] nib;\n"
      "class C #(nib P = 12'hFFF);\n"
      "endclass\n"
      "module m;\n"
      "  localparam int Q = C#()::P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "Q"), 15);
}

TEST(TypedefParameterType, PackageParameterOfASignedTypedefReadsSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef byte sb;\n"
      "  parameter sb B = 8'd200;\n"
      "endpackage\n"
      "module m;\n"
      "  localparam int Q = p::B;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "Q"), -56);
}

TEST(TypedefParameterType, DimensionsOnASignedTypedefMakeAnUnsignedArray) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef byte sb;\n"
      "  parameter sb [1:0] W = 20'hFFFFF;\n"
      "  parameter sb [1:0] F = '1;\n"
      "endpackage\n"
      "module m;\n"
      "  localparam int QW = p::W;\n"
      "  localparam int QF = p::F;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "QW"), 65535);
  EXPECT_EQ(ParamValue(design, "QF"), 65535);
}

TEST(TypedefParameterType, TypedefRangeNamingAPackageParameterSizesTheCut) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter int N = 4;\n"
      "  typedef bit [N-1:0] t;\n"
      "  parameter t P = 12'hFFF;\n"
      "endpackage\n"
      "module m;\n"
      "  localparam int Q = p::P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "Q"), 15);
}

TEST(TypedefParameterType, ClassBodyParameterOfTheClassTypedefIsCut) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  typedef int u;\n"
      "  typedef bit [3:0] t;\n"
      "  localparam t P = 12'hFFF;\n"
      "endclass\n"
      "module m;\n"
      "  localparam int Q = C::P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "Q"), 15);
}

TEST(TypedefParameterType, SpecializationReadsTheClassTypedefOverTheUnits) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "typedef byte t;\n"
      "class D #(int W = 1);\n"
      "  typedef bit [3:0] t;\n"
      "  localparam t P = 12'hFFF;\n"
      "endclass\n"
      "module m;\n"
      "  localparam int Q = D#()::P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "Q"), 15);
}

TEST(TypedefParameterType, ModuleClassParameterOfTheClassTypedefIsCut) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class C;\n"
      "    typedef bit [3:0] t;\n"
      "    localparam t P = 12'hFFF;\n"
      "  endclass\n"
      "  logic [C::P-1:0] v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* v = FindVar(design, "m", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 15u);
}

TEST(TypedefParameterType, NestedClassParameterOfItsOwnTypedefIsCut) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Outer;\n"
      "  class Inner;\n"
      "    typedef bit [3:0] t;\n"
      "    localparam t P = 12'hFFF;\n"
      "  endclass\n"
      "endclass\n"
      "module m;\n"
      "  localparam int Q = Outer::Inner::P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "Q"), 15);
}

TEST(TypedParameterSign, TimeParameterIsSixtyFourUnsignedBits) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam time T = -1;\n"
      "  localparam int BT = $bits(T);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "BT"), 64);
  const auto* t = FindParam(design, "m", "T");
  ASSERT_NE(t, nullptr);
  EXPECT_EQ(t->decl_width, 64u);
  EXPECT_FALSE(t->decl_is_signed);
}

TEST(TypedefParameterType, ParameterOfARealTypedefIsReal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "typedef shortreal sr_t;\n"
      "typedef real r_t;\n"
      "module m #(parameter sr_t P = 2.75);\n"
      "  localparam r_t Q = 2.75;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  for (const char* name : {"P", "Q"}) {
    const auto* p = FindParam(design, "m", name);
    ASSERT_NE(p, nullptr) << name;
    EXPECT_TRUE(p->is_real_value) << name;
    EXPECT_DOUBLE_EQ(p->resolved_real, 2.75) << name;
  }
}

}  // namespace
