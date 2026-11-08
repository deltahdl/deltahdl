#include <gtest/gtest.h>

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

}  // namespace
