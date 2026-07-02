#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ExpressionElaboration, IndexedPartSelectElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial x = data[0+:8];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, ConstantRangePackedDimElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial x = data[7:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PrimaryElaboration, PrimaryHierIdentSelectElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  logic x;\n"
      "  initial x = data[3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, GenvarExprElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int N = 4;\n"
      "  logic [N-1:0] w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
TEST(VarLvaluePartSelect, VarLvaluePartSelect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'h00; x[7:4] = 4'hF; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xF0u);
}

TEST(SelectElaboration, ScalarBitSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic x;\n"
      "  logic y;\n"
      "  assign y = x[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(SelectElaboration, ScalarPartSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic x;\n"
      "  logic [3:0] y;\n"
      "  assign y = x[3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(SelectElaboration, IndexedPartSelectWidthMustBeConstant) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [15:0] data;\n"
      "  integer w;\n"
      "  logic [7:0] y;\n"
      "  initial begin w = 8; y = data[0+:w]; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §11.5.1/§11.2.1: the indexed part-select width is a constant expression,
// which may be a parameter reference. It must be evaluated in the module's
// parameter scope, not rejected as non-constant (contrast the `integer w`
// variable case above, which is genuinely non-constant and still errors).
TEST(SelectElaboration, IndexedPartSelectWidthParameterAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  parameter integer c = 3;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] y;\n"
      "  initial y = data[1+:c];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SelectElaboration, IndexedPartSelectWidthMustBePositive) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] y;\n"
      "  assign y = data[0+:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(SelectElaboration, RealVariableBitSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  logic y;\n"
      "  assign y = r[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(SelectElaboration, RealVariablePartSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  logic [3:0] y;\n"
      "  assign y = r[3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(SelectElaboration, NonIndexedPartSelectBoundsMustBeConstant) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [15:0] data;\n"
      "  integer w;\n"
      "  logic [7:0] y;\n"
      "  assign y = data[w:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(SelectElaboration, PartSelectReversedOrderError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] y;\n"
      "  assign y = data[0:7];\n"
      "endmodule\n",
      f);
  // data is declared descending [15:0], so the first index must be the larger
  // one; data[0:7] reverses that and is illegal.
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(SelectElaboration, PartSelectAscendingOrderOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [0:15] data;\n"
      "  logic [7:0] y;\n"
      "  assign y = data[0:7];\n"
      "endmodule\n",
      f);
  // For an ascending [0:15] declaration the lower index is the more
  // significant bit, so data[0:7] is a correctly ordered part-select.
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(SelectElaboration, RealParameterSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter real P = 1.5;\n"
      "  logic y;\n"
      "  assign y = P[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §11.5.1 lists a packed structure among the operands a bit-select may
// address. A packed struct presents as a single contiguous vector, so a
// bit-select of it must elaborate without the "select of a scalar" error.
TEST(SelectElaboration, PackedStructBitSelectIsLegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  struct packed { logic [3:0] hi; logic [3:0] lo; } s;\n"
      "  logic b;\n"
      "  initial b = s[0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §11.5.1: the same operand rule admits a part-select of a packed structure.
TEST(SelectElaboration, PackedStructPartSelectIsLegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  struct packed { logic [3:0] hi; logic [3:0] lo; } s;\n"
      "  logic [3:0] y;\n"
      "  initial y = s[7:4];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §11.5.1/§7.4.1: the packed-structure select base is reached through a
// typedef as well -- a named packed struct type is still a single vector and
// remains part-selectable.
TEST(SelectElaboration, NamedPackedStructPartSelectIsLegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } s_t;\n"
      "  s_t s;\n"
      "  logic [3:0] y;\n"
      "  initial y = s[7:4];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §11.5.1: a packed union likewise collapses to a single vector, so a
// part-select of a packed union is a legal select base.
TEST(SelectElaboration, PackedUnionPartSelectIsLegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } u;\n"
      "  logic [3:0] y;\n"
      "  initial y = u[7:4];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §11.5.1 negative: an unpacked structure is not a single vector, so a
// bit-select of it stays illegal. Confirms the packed-aggregate allowance is
// narrow and does not leak to unpacked aggregates.
TEST(SelectElaboration, UnpackedStructBitSelectIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct { logic [3:0] hi; logic [3:0] lo; } s;\n"
      "  logic b;\n"
      "  initial b = s[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §11.5.1/§11.2.1: the indexed part-select width is a constant expression,
// which a localparam satisfies just as a parameter does. It must resolve in the
// module's constant scope rather than be rejected as non-constant (the
// parameter form is covered separately by
// IndexedPartSelectWidthParameterAccepted).
TEST(SelectElaboration, IndexedPartSelectWidthLocalparamAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  localparam integer c = 3;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] y;\n"
      "  initial y = data[1+:c];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.5.1: a bit-select of a real-typed variable is illegal, and the rule
// covers the whole real family -- shortreal is a real type just as `real` is.
TEST(SelectElaboration, ShortrealVariableBitSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  shortreal r;\n"
      "  logic y;\n"
      "  assign y = r[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §11.5.1: realtime is likewise a real type, so selecting from it is illegal.
TEST(SelectElaboration, RealtimeVariableBitSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  realtime r;\n"
      "  logic y;\n"
      "  assign y = r[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §11.5.1: for an ascending [0:15] declaration the smaller index names the more
// significant bit, so data[7:0] reverses the required ordering and is illegal
// (the descending-declaration form is covered by PartSelectReversedOrderError).
TEST(SelectElaboration, AscendingDeclReversedPartSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [0:15] data;\n"
      "  logic [7:0] y;\n"
      "  assign y = data[7:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}
