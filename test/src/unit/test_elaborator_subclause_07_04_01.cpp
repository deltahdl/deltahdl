#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(PackedArrayValidation, PackedDimOnByte_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  byte [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed dimensions cannot be added to an integer "
                            "type whose width is already fixed",
                            2, "7.4.1"));
}

TEST(PackedArrayValidation, PackedDimOnShortint_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  shortint [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed dimensions cannot be added to an integer "
                            "type whose width is already fixed",
                            2, "7.4.1"));
}

TEST(PackedArrayValidation, PackedDimOnInt_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed dimensions cannot be added to an integer "
                            "type whose width is already fixed",
                            2, "7.4.1"));
}

TEST(PackedArrayValidation, PackedDimOnLongint_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  longint [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed dimensions cannot be added to an integer "
                            "type whose width is already fixed",
                            2, "7.4.1"));
}

TEST(PackedArrayValidation, PackedDimOnInteger_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  integer [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed dimensions cannot be added to an integer "
                            "type whose width is already fixed",
                            2, "7.4.1"));
}

TEST(PackedArrayValidation, PackedDimOnTime_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  time [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed dimensions cannot be added to an integer "
                            "type whose width is already fixed",
                            2, "7.4.1"));
}

TEST(PackedArrayValidation, PackedDimOnLogic_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [7:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnBit_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  bit [7:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnReg_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  reg [7:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimElaboratesWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [7:0] x; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "x");
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(PackedArrayValidation, XzInPackedDimLeft_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1'bx:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed dimension range shall not contain x or z",
                            2, "7.4.1"));
}

TEST(PackedArrayValidation, XzInPackedDimRight_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [7:1'bz] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed dimension range shall not contain x or z",
                            2, "7.4.1"));
}

TEST(PackedArrayValidation, XzInExtraPackedDim_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [3:0][1'bx:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed dimension range shall not contain x or z",
                            2, "7.4.1"));
}

TEST(PackedArrayValidation, MultiDimPackedArrayWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0][7:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 32u);
}

TEST(PackedArrayValidation, PackedDimOnEnumBaseType_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum logic [1:0] {A, B, C} e_t;\n"
      "  e_t x;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, AnEnumArrayWithNoBaseTypeTakesAnElementSelect) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum {P, Q} [1:0] pair_t;\n"
      "  pair_t w;\n"
      "  enum {R, S} [2:0] v;\n"
      "  initial begin\n"
      "    w[1] = Q;\n"
      "    v[2] = S;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PackedArrayValidation, PackedDimOnReal_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed array element type must be a single-bit "
                            "type, an enumerated type, a packed array, or a "
                            "packed structure or union",
                            2, "7.4.1"));
}

TEST(PackedArrayValidation, PackedDimOnShortreal_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  shortreal [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "packed array element type must be a single-bit type", 2, "7.4.1"));
}

TEST(PackedArrayValidation, PackedDimOnRealtime_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  realtime [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "packed array element type must be a single-bit type", 2, "7.4.1"));
}

TEST(PackedArrayValidation, PackedDimOnString_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  string [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "packed array element type must be a single-bit type", 2, "7.4.1"));
}

TEST(PackedArrayValidation, PackedDimOnChandle_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "packed array element type must be a single-bit type", 2, "7.4.1"));
}

TEST(PackedArrayValidation, PackedDimOnEvent_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  event [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "packed array element type must be a single-bit type", 2, "7.4.1"));
}

TEST(PackedArrayValidation, DescendingPackedRange_Allowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [0:7] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(PackedArrayValidation, LargePackedArrayAtLeast65536Bits_Accepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [65535:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 65536u);
}

TEST(PackedArrayValidation, SignedPackedArrayMarkedSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic signed [7:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_signed);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(PackedArrayValidation, NegativeBoundsInPackedRange_Allowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [-1:-4] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 4u);
}

TEST(PackedArrayValidation, EqualBoundsInPackedRange_Allowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:3] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 1u);
}

TEST(PackedArrayValidation, PackedDimOnPackedStruct_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } s_t;\n"
      "  s_t [3:0] arr;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimParameterBoundWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter integer W = 8;\n"
      "  logic [W-1:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  const RtlirVariable* x = nullptr;
  for (const auto& v : mod->variables)
    if (v.name == "x") x = &v;
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 8u);
}

TEST(PackedArrayValidation, PackedDimLocalparamBoundWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam integer W = 8;\n"
      "  logic [W-1:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  const RtlirVariable* x = nullptr;
  for (const auto& v : mod->variables)
    if (v.name == "x") x = &v;
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 8u);
}

TEST(PackedArrayValidation, PackedDimOnIntNames7_4_1) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed dimensions cannot be added to an integer "
                            "type whose width is already fixed",
                            2, "7.4.1"));
}

TEST(PackedArrayValidation, ElementTypeJudgedThroughTypedefNames) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef real r_t;\n"
      "  typedef int i_t;\n"
      "  typedef i_t ii_t;\n"
      "  typedef struct { int a; } u_t;\n"
      "  class C; endclass\n"
      "  r_t [3:0] a;\n"
      "  ii_t [1:0] b;\n"
      "  u_t [1:0] c;\n"
      "  C [1:0] h;\n"
      "  typedef bit [1:5] bsix;\n"
      "  typedef struct packed { bit x; } ps_t;\n"
      "  typedef union soft { bit [1:0] p; bit q; } su_t;\n"
      "  bsix [1:10] d;\n"
      "  ps_t [1:0] e;\n"
      "  su_t [1:0] g;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "packed array element type must be a single-bit type", 7,
      "7.4.1"));
  EXPECT_TRUE(ReportedError(diags,
                            "packed dimensions cannot be added to an integer "
                            "type whose width is already fixed",
                            8, "7.4.1"));
  EXPECT_TRUE(ReportedError(
      diags, "packed array element type must be a single-bit type", 9,
      "7.4.1"));
  EXPECT_TRUE(ReportedError(
      diags, "packed array element type must be a single-bit type", 10,
      "7.4.1"));
  for (const auto& d : diags) {
    EXPECT_NE(d.loc.line, 14u) << d.message;
    EXPECT_NE(d.loc.line, 15u) << d.message;
    EXPECT_NE(d.loc.line, 16u) << d.message;
  }
}

constexpr std::string_view kFixedWidth =
    "packed dimensions cannot be added to an integer type whose width is "
    "already fixed";
constexpr std::string_view kElementType =
    "packed array element type must be a single-bit type";

TEST(PackedArrayValidation,
     FixedWidthIntegerPackedDimReportedInModuleInterfaceProgramAndGenerate) {
  ElabFixture f;
  ElaborateSrc(
      "typedef int int_t;\n"
      "typedef logic [7:0] l8_t;\n"
      "interface ifc #(type T = byte);\n"
      "  int [1:0] a;\n"
      "  int_t [1:0] b;\n"
      "  T [1:0] c;\n"
      "  l8_t [1:0] ok;\n"
      "endinterface\n"
      "program pr #(type T = byte);\n"
      "  int [1:0] a;\n"
      "  int_t [1:0] b;\n"
      "  T [1:0] c;\n"
      "  l8_t [1:0] ok;\n"
      "endprogram\n"
      "module top #(type T = shortint);\n"
      "  int [1:0] a;\n"
      "  int_t [1:0] b;\n"
      "  T [1:0] c;\n"
      "  l8_t [1:0] ok;\n"
      "  typedef int_t [1:0] td_t;\n"
      "  typedef l8_t [1:0] tdok_t;\n"
      "  if (1) begin : g\n"
      "    int [1:0] ga;\n"
      "    int_t [1:0] gb;\n"
      "    T [1:0] gc;\n"
      "    l8_t [1:0] gok;\n"
      "  end\n"
      "  ifc ii();\n"
      "  pr p();\n"
      "endmodule\n",
      f);
  for (uint32_t line : {4, 5, 6, 10, 11, 12, 16, 17, 18, 20, 23, 24, 25}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kFixedWidth, line, "7.4.1"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 13u);
}

TEST(
    PackedArrayValidation,
    DISABLED_FixedWidthIntegerPackedDimReportedInCompilationUnitPackageAndClass) {
  ElabFixture f;
  ElaborateSrc(
      "typedef int int_t;\n"
      "typedef logic [7:0] l8_t;\n"
      "int [1:0] cu_a;\n"
      "int_t [1:0] cu_b;\n"
      "l8_t [1:0] cu_ok;\n"
      "package pk;\n"
      "  byte [1:0] p_a;\n"
      "  int_t [1:0] p_b;\n"
      "  l8_t [1:0] p_ok;\n"
      "endpackage\n"
      "class C #(type T = int);\n"
      "  int [1:0] c_a;\n"
      "  static int_t [1:0] c_b;\n"
      "  T [1:0] c_c;\n"
      "  l8_t [1:0] c_ok;\n"
      "  function void m(int [1:0] fa);\n"
      "    int_t [1:0] fl;\n"
      "    l8_t [1:0] flok;\n"
      "  endfunction\n"
      "endclass\n"
      "class D #(type T = l8_t);\n"
      "  T [1:0] d_a;\n"
      "endclass\n"
      "module top;\n"
      "  C cc;\n"
      "  D #(int) dd;\n"
      "  D dok;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3, 4, 7, 8, 12, 13, 14, 16, 17, 22}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kFixedWidth, line, "7.4.1"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 10u);
}

TEST(
    PackedArrayValidation,
    DISABLED_FixedWidthIntegerPackedDimReportedInSubroutinesBlocksMembersPortsAndParameters) {
  ElabFixture f;
  ElaborateSrc(
      "typedef int int_t;\n"
      "typedef logic [7:0] l8_t;\n"
      "module sub(input var int [1:0] pa, input var l8_t [1:0] pok);\n"
      "endmodule\n"
      "module mp #(parameter int_t [1:0] P = 0, parameter l8_t [1:0] Q = 0);\n"
      "endmodule\n"
      "module top #(type T = shortint);\n"
      "  function automatic void f(int [1:0] fa, l8_t [1:0] fok);\n"
      "    int_t [1:0] fl;\n"
      "    T [1:0] ft;\n"
      "    l8_t [1:0] flok;\n"
      "  endfunction\n"
      "  task automatic t(int_t [1:0] ta);\n"
      "    integer [1:0] tl;\n"
      "  endtask\n"
      "  initial begin\n"
      "    time [1:0] bl;\n"
      "    int_t [1:0] bb;\n"
      "    T [1:0] bt;\n"
      "    l8_t [1:0] bok;\n"
      "  end\n"
      "  struct packed {\n"
      "    longint [1:0] sa;\n"
      "    int_t [1:0] sb;\n"
      "    T [1:0] sc;\n"
      "    l8_t sok;\n"
      "  } s;\n"
      "  sub u(.pa(0), .pok(0));\n"
      "  mp m();\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3, 5, 8, 9, 10, 13, 14, 17, 18, 19, 23, 24, 25}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kFixedWidth, line, "7.4.1"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 13u);
}

TEST(PackedArrayValidation,
     VirtualInterfaceUnpackedUnionAndInterfaceClassElementsReported) {
  ElabFixture f;
  ElaborateSrc(
      "interface I; endinterface\n"
      "interface class IC; endclass\n"
      "typedef virtual I vi_t;\n"
      "typedef union { bit a; } uu_t;\n"
      "typedef struct packed { bit [7:0] a; } ps_t;\n"
      "typedef enum bit [1:0] { A, B } e_t;\n"
      "typedef union packed { bit [7:0] a; } pu_t;\n"
      "module top;\n"
      "  vi_t [1:0] v;\n"
      "  uu_t [1:0] u;\n"
      "  IC [1:0] h;\n"
      "  bit [1:0][7:0] ok1;\n"
      "  ps_t [1:0] ok2;\n"
      "  e_t [1:0] ok3;\n"
      "  pu_t [1:0] ok4;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {9, 10, 11}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kElementType, line, "7.4.1"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(PackedArrayValidation,
     DISABLED_UnpackedArrayDynamicArrayAndQueueTypedefElementsReported) {
  ElabFixture f;
  ElaborateSrc(
      "typedef bit ua_t [2];\n"
      "typedef bit da_t [];\n"
      "typedef bit q_t [$];\n"
      "typedef struct packed { bit [7:0] a; } ps_t;\n"
      "module top;\n"
      "  ua_t [1:0] x1;\n"
      "  da_t [1:0] x2;\n"
      "  q_t [1:0] x3;\n"
      "  ps_t [1:0] ok;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {6, 7, 8}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kElementType, line, "7.4.1"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(
    PackedArrayValidation,
    DISABLED_ForbiddenElementTypesReportedInPackagesClassesMembersAndReturnTypes) {
  ElabFixture f;
  ElaborateSrc(
      "interface I; endinterface\n"
      "interface class IC; endclass\n"
      "typedef virtual I vi_t;\n"
      "typedef bit ua_t [2];\n"
      "typedef bit da_t [];\n"
      "typedef bit q_t [$];\n"
      "typedef union { bit a; } uu_t;\n"
      "typedef struct packed { bit [7:0] a; } ps_t;\n"
      "package pk;\n"
      "  uu_t [1:0] p1;\n"
      "  vi_t [1:0] p2;\n"
      "  ps_t [1:0] pok;\n"
      "endpackage\n"
      "class K;\n"
      "  IC [1:0] k1;\n"
      "  uu_t [1:0] k2;\n"
      "  ps_t [1:0] kok;\n"
      "endclass\n"
      "typedef struct {\n"
      "  uu_t [1:0] m1;\n"
      "  vi_t [1:0] m2;\n"
      "  ps_t [1:0] mok;\n"
      "} us_t;\n"
      "module top;\n"
      "  function automatic uu_t [1:0] g();\n"
      "  endfunction\n"
      "  function automatic IC [1:0] h();\n"
      "  endfunction\n"
      "  function automatic ps_t [1:0] ok();\n"
      "  endfunction\n"
      "  us_t s;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {10, 11, 15, 16, 20, 21, 25, 27}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kElementType, line, "7.4.1"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 8u);
}

TEST(PackedArrayValidation,
     FixedWidthIntegerPackedDimReportedThroughATypeParameterOverride) {
  ElabFixture f;
  ElaborateSrc(
      "module sub #(type T = logic [7:0]);\n"
      "  T [1:0] x;\n"
      "endmodule\n"
      "module top;\n"
      "  sub #(.T(int)) a();\n"
      "  sub #(.T(logic [3:0])) b();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kFixedWidth, 2, "7.4.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
