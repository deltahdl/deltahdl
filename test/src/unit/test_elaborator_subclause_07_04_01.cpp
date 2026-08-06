#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(PackedArrayValidation, PackedDimOnByte_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  byte [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnShortint_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  shortint [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnInt_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnLongint_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  longint [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnInteger_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  integer [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnTime_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  time [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
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
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, XzInPackedDimRight_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [7:1'bz] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, XzInExtraPackedDim_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [3:0][1'bx:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
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

TEST(PackedArrayValidation, PackedDimOnReal_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnShortreal_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  shortreal [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnRealtime_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  realtime [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnString_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  string [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnChandle_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(PackedArrayValidation, PackedDimOnEvent_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  event [3:0] x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
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

}  // namespace
