#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "common/diagnostic.h"
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

struct ValueSource {
  const char* where;
  const char* src;
  const char* message;
  uint32_t line;
  const char* subclause;
};

TEST(ValueParameters, ValueSetFromAVariableANetOrAHierarchicalNameIsReported) {
  const ValueSource kSources[] = {
      {"module body parameter from a variable",
       "module m;\n  int x;\n  parameter int P = x;\nendmodule\n",
       "parameter 'P' value is not a constant expression", 3, "6.20.2"},
      {"module body parameter from a net",
       "module m;\n  wire w;\n  parameter int P = w + 1;\nendmodule\n",
       "parameter 'P' value is not a constant expression", 3, "6.20.2"},
      {"interface body parameter from a variable",
       "interface i;\n  int x;\n  parameter int P = x;\nendinterface\n"
       "module m;\n  i u();\nendmodule\n",
       "parameter 'P' value is not a constant expression", 3, "6.20.2"},
      {"program body parameter from a variable",
       "program p;\n  int x;\n  parameter int P = x;\nendprogram\n"
       "module m;\n  p u();\nendmodule\n",
       "parameter 'P' value is not a constant expression", 3, "6.20.2"},
      {"module port list parameter from a compilation-unit variable",
       "int v;\nmodule m #(parameter int P = v);\nendmodule\n",
       "parameter 'P' value is not a constant expression", 2, "6.20.2"},
      {"interface port list parameter from a compilation-unit variable",
       "int v;\ninterface i #(parameter int P = v);\nendinterface\n"
       "module m;\n  i u();\nendmodule\n",
       "parameter 'P' value is not a constant expression", 2, "6.20.2"},
      {"program port list parameter from a compilation-unit variable",
       "int v;\nprogram p #(parameter int P = v);\nendprogram\n"
       "module m;\n  p u();\nendmodule\n",
       "parameter 'P' value is not a constant expression", 2, "6.20.2"},
      {"module port list localparam from a compilation-unit variable",
       "int v;\nmodule m #(localparam int P = v);\nendmodule\n",
       "localparam 'P' initializer is not a constant expression", 2, "6.20.4"},
      {"module body specparam from a variable",
       "module m;\n  int v;\n  specparam t = v;\nendmodule\n",
       "specparam 't' value is not a constant expression", 3, "6.20.2"},
      {"module body specparam whose typical value is a variable",
       "module m;\n  int v;\n  specparam t = 1:v:3;\nendmodule\n",
       "specparam 't' value is not a constant expression", 3, "6.20.2"},
      {"specify block specparam from a variable",
       "module m(input a, output b);\n  int v;\n  specify\n"
       "    specparam t = v;\n  endspecify\nendmodule\n",
       "specparam 't' value is not a constant expression", 4, "6.20.2"},
      {"specify block PATHPULSE$ specparam with a variable error limit",
       "module m(input a, output b);\n  int v;\n  specify\n"
       "    specparam PATHPULSE$ = (1, v);\n  endspecify\nendmodule\n",
       "specparam 'PATHPULSE$' value is not a constant expression", 4,
       "6.20.2"},
      {"module body specparam from a hierarchical name",
       "module c;\n  int x;\nendmodule\nmodule m;\n  c u();\n"
       "  specparam t = u.x;\nendmodule\n",
       "specparam 't' value contains a hierarchical reference", 6, "6.20.2"},
      {"specify block specparam from a hierarchical name",
       "module c;\n  int x;\nendmodule\nmodule m(input a, output b);\n"
       "  c u();\n  specify\n    specparam t = u.x;\n  endspecify\n"
       "endmodule\n",
       "specparam 't' value contains a hierarchical reference", 7, "6.20.2"},
      {"class port parameter from a hierarchical name",
       "module top;\n  int x;\nendmodule\nclass C #(int P = top.x);\n"
       "endclass\n",
       "class parameter 'P' value is not a constant expression", 4, "6.20.2"},
      {"class body parameter from a hierarchical name",
       "module top;\n  int x;\nendmodule\nclass C;\n"
       "  parameter int P = top.x;\nendclass\n",
       "class parameter 'P' value is not a constant expression", 5, "6.20.2"},
  };
  for (const ValueSource& source : kSources) {
    SCOPED_TRACE(source.where);
    ElabFixture f;
    ElaborateSrc(source.src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), source.message, source.line,
                              source.subclause));
  }
}

TEST(ValueParameters, ValueSetFromConstantsAndAggregateMembersIsAccepted) {
  const char* const kSources[] = {
      "module m;\n  localparam int L = 2;\n  parameter int P = L + 1;\n"
      "endmodule\n",
      "module m;\n  parameter int A[2] = '{1, 2};\n"
      "  parameter int B = A[1];\n  localparam int C = A[0];\nendmodule\n",
      "module m;\n  typedef struct packed { int a; int b; } s_t;\n"
      "  parameter s_t S = '{a: 3, b: 4};\n  parameter int W = S.b;\n"
      "  localparam int L = S.a;\nendmodule\n",
      "module m;\n  typedef struct { int a; int b; } s_t;\n"
      "  parameter s_t S = '{3, 4};\n  parameter int W = S.b;\n"
      "  localparam int L = S.a;\nendmodule\n",
      "interface i;\n  localparam int L = 2;\n  parameter int P = L;\n"
      "endinterface\nmodule m;\n  i u();\nendmodule\n",
      "program p;\n  localparam int L = 2;\n  parameter int P = L;\n"
      "endprogram\nmodule m;\n  p u();\nendmodule\n",
      "parameter int CP = 3;\nmodule m #(parameter int P = CP);\n"
      "endmodule\n",
      "parameter int CP = 3;\ninterface i #(parameter int P = CP);\n"
      "endinterface\nmodule m;\n  i u();\nendmodule\n",
      "parameter int CP = 3;\nprogram p #(parameter int P = CP);\n"
      "endprogram\nmodule m;\n  p u();\nendmodule\n",
      "parameter int CP = 3;\nmodule m #(localparam int P = CP);\n"
      "endmodule\n",
      "module m;\n  parameter int P = 2;\n  specparam t = P + 1;\n"
      "  specparam u = 1:P:3;\n  specparam w = t;\nendmodule\n",
      "module m(input a, output b);\n  parameter int P = 2;\n  specify\n"
      "    specparam t = P;\n    specparam u = t:t + 1:t + 2;\n"
      "    specparam PATHPULSE$ = (P, P + 1);\n  endspecify\nendmodule\n",
      "package pk;\n  parameter int N = 4;\nendpackage\n"
      "class C #(int P = pk::N);\n  parameter int Q = pk::N + 1;\n"
      "endclass\n",
  };
  for (const char* src : kSources) {
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    for (const Diagnostic& diag : f.diag.Diagnostics()) {
      if (diag.severity == DiagSeverity::kError)
        ADD_FAILURE() << "line " << diag.loc.line << ": " << diag.message;
    }
  }
}

constexpr const char* kStructureDesign =
    "typedef struct { int a; logic [7:0] b; } s_t;\n"
    "module sub;\n"
    "  parameter s_t P = '{a: 1, b: 8'h2};\n"
    "  parameter s_t S [2] = '{'{a: 0, b: 8'h0}, '{a: 1, b: 8'h1}};\n"
    "  parameter int A[2] = '{1, 2};\n"
    "  localparam s_t L = '{a: 1, b: 8'h2};\n"
    "endmodule\n"
    "interface ifc;\n"
    "  parameter s_t P = '{a: 1, b: 8'h2};\n"
    "endinterface\n";

TEST(AggregateParameters, DefparamNamingAPartOfAParameterIsReported) {
  ElabFixture f;
  ElaborateSrc(std::string(kStructureDesign) +
                   "module top;\n"
                   "  parameter s_t Q = '{a: 3, b: 8'h4};\n"
                   "  sub u();\n"
                   "  ifc i();\n"
                   "  if (1) begin : g\n"
                   "    sub w();\n"
                   "  end\n"
                   "  defparam u.P.a = 5;\n"
                   "  defparam u.S[1].b = 8'h6;\n"
                   "  defparam i.P.b = 8'h7;\n"
                   "  defparam Q.a = 9;\n"
                   "  defparam top.u.P.b = 8'h8;\n"
                   "  defparam g.w.P.a = 4;\n"
                   "  defparam u.L = '{a: 2, b: 8'h3};\n"
                   "endmodule\n",
               f);
  for (uint32_t line : {18u, 19u, 20u, 21u, 22u, 23u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "defparam names a part of parameter", line,
                              "6.20.2"))
        << "line " << line;
  }
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "defparam cannot override a local parameter", 24,
                            "23.10.1"));
}

TEST(AggregateParameters,
     DefparamNamingAnElementOrABlockParameterPartIsReported) {
  ElabFixture f;
  RtlirDesign* design =
      ElaborateSrc(std::string(kStructureDesign) +
                       "module top;\n"
                       "  parameter int B[2] = '{1, 2};\n"
                       "  sub u();\n"
                       "  if (1) begin : h\n"
                       "    parameter s_t P = '{a: 1, b: 8'h2};\n"
                       "  end\n"
                       "  for (genvar i = 0; i < 2; i++) begin : l\n"
                       "    parameter s_t P = '{a: i, b: 8'h2};\n"
                       "  end\n"
                       "  defparam u.A[0] = 5;\n"
                       "  defparam u.S[1] = '{a: 2, b: 8'h3};\n"
                       "  defparam B[1] = 5;\n"
                       "  defparam top.B[0] = 6;\n"
                       "  defparam h.P.a = 4;\n"
                       "  defparam top.h.P.b = 8'h5;\n"
                       "  defparam l[1].P.a = 7;\n"
                       "endmodule\n",
                   f);
  const std::pair<uint32_t, const char*> kParts[] = {
      {20, "'A'"}, {21, "'S'"}, {22, "'B'"}, {23, "'B'"},
      {24, "'P'"}, {25, "'P'"}, {26, "'P'"}};
  for (const auto& [line, name] : kParts) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(),
                      std::string("defparam names a part of parameter ") + name,
                      line, "6.20.2"))
        << "line " << line;
  }
  const RtlirModule* top = FindModule(design, "top");
  ASSERT_NE(top, nullptr);
  for (const auto& p : top->params) EXPECT_FALSE(p.from_override) << p.name;
  for (const auto& child : top->children) {
    for (const auto& p : child.resolved->params) {
      EXPECT_FALSE(p.from_override) << p.name;
    }
  }
}

TEST(AggregateParameters, DefparamOfAWholeAggregateParameterIsAccepted) {
  ElabFixture f;
  ElaborateSrc(std::string(kStructureDesign) +
                   "module top;\n"
                   "  parameter s_t Q = '{a: 3, b: 8'h4};\n"
                   "  sub u();\n"
                   "  ifc i();\n"
                   "  if (1) begin : g\n"
                   "    sub w();\n"
                   "  end\n"
                   "  defparam u.P = '{a: 5, b: 8'h6};\n"
                   "  defparam u.S = '{'{a: 1, b: 8'h1}, '{a: 2, b: 8'h2}};\n"
                   "  defparam u.A = '{3, 4};\n"
                   "  defparam i.P = '{a: 7, b: 8'h7};\n"
                   "  defparam top.Q = '{a: 9, b: 8'h9};\n"
                   "  defparam g.w.P = '{a: 4, b: 8'h4};\n"
                   "endmodule\n",
               f);
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    ADD_FAILURE() << "line " << diag.loc.line << ": " << diag.message;
  }
}

}  // namespace
