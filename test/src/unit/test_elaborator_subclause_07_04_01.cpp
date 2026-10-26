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

// §7.4.1 lets the bounds of every packed dimension of a packed array
// declaration be any integer, positive, negative or zero, so long as no bit is
// x or z, so it governs the first dimension exactly as it governs a later one.
// These two cases put the x and the z in the first dimension;
// XzInExtraPackedDim_Rejected puts one in a later dimension.
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

// §7.4.1 with A.2.2.1: packed dimensions after an enumeration's body make a
// packed array of the enumeration, written in the declaration or through a
// typedef, and with no base type each element is an int (§6.19). An index on
// either selects an element, which §11.5.1's rule on selecting a scalar does
// not reach.
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

// The report names the element types §7.4.1 lets a packed array be made of,
// in the standard's own terms: Annex P keeps "aggregate" for unpacked
// structures, unions and arrays, so a packed one is never called that.
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
  // Bounds in a packed range may be any integer, including negative
  // values; width is determined by the absolute difference plus one.
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
  // When both range bounds are equal, the packed array degenerates to a
  // single bit — exercising the "equal to" case of the range rule.
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
  // The recursive half of the allowed-element-types rule: a packed
  // structure may itself be the element type of an enclosing packed
  // array dimension.
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
  // Each packed-dimension bound is a constant expression that may be any
  // integer value; a parameter is such a constant. `logic [W-1:0]` with W==8
  // must elaborate to an 8-bit vector, i.e. the parameter bound is evaluated
  // rather than ignored. (The literal-bound form is PackedDimElaboratesWidth.)
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
  // A localparam bound is likewise a constant expression and takes the
  // localparam evaluation path rather than the parameter one.
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

// §7.4.1: the integer types with predefined widths, byte, shortint, int,
// longint, integer and time, take no declared packed array dimension. The
// message on the report is what tells this rejection from the x-or-z rule
// §7.4.1 states for a range bound, which the same bracketed dimension breaches
// when its bounds rather than its type are at fault. This case reaches the
// check through ElabOk, which preprocesses the source first, where
// PackedDimOnInt_Rejected reaches it through ElaborateSrc.
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

// §7.4.4 lets packed dimensions be added in stages through a typedef, so the
// element type of a packed dimension written after a typedef name is the type
// the name stands for, followed through a chain of names, and §7.4.1 judges
// that. A packed structure or soft union behind the name is a packed element; a
// real, an unpacked structure or a class is not, and an int takes no packed
// dimension at all.
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
