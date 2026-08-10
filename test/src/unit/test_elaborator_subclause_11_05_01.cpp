#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_rtlir_lookup.h"

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

// §11.5.1: the first index of a part-select shall address a more significant
// bit than the second, so v[4:7] is illegal on a vector that counts downward.
// The vector is declared [7:4] rather than [7:0] so that an index and the
// storage offset it reaches are different numbers: on [7:0] the two coincide,
// and a check that computed an offset where §11.5.1 requires an index would
// answer this case the same way as the rule does.
TEST(SelectElaboration, ReversedPartSelectOfANonZeroBasedVectorNames11_5_1) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic [7:4] v;\n"
             "  logic [3:0] result;\n"
             "  initial result = v[4:7];\n"
             "endmodule\n",
             f));
  const auto* diag =
      FindDiag(f, "part-select's first index must address a more");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "11.5.1");
}

}  // namespace
TEST(VarLvaluePartSelect, VarLvaluePartSelect) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'h00; x[7:4] = 4'hF; end\n"
      "endmodule\n",
      f, "x");
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

// §11.5.1: "Bit-selects extract a particular bit from a vector, packed array,
// packed structure, parameter, or concatenation", and "The actual bit that is
// accessed by an address is, in part, determined by the declaration of acc" --
// the clause sets `logic [15:0] acc` beside `logic [2:17] acc` and observes
// that one value of an index reaches a different bit in each. A parameter is
// one of the operands named there, so a select on one is addressed over the
// range the parameter was declared with.
//
// P is declared [8:1], so index 8 names its most significant bit and index 1
// its least, and 8'b1010_0101 puts a 1 at index 8. Reading the index as a
// distance above the least significant end instead asks for the ninth bit of
// an eight-bit value and answers 0.
//
// The range is written [8:1] rather than [7:0] deliberately. Where a
// declaration ends at 0 the index of a bit and its distance from the least
// significant end are the same number, so code that confuses the two returns
// the right answer and a test built on that spelling passes whether the rule is
// implemented or not.
TEST(SelectElaboration, ParameterBitSelectIsAddressedOverItsDeclaredRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [8:1] P = 8'b1010_0101;\n"
      "  localparam B = P[8];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* b = FindParam(design, "m", "B");
  ASSERT_NE(b, nullptr);
  EXPECT_TRUE(b->is_resolved);
  EXPECT_EQ(b->resolved_value, 1);
}

// The same rule for a part-select, which §11.5 admits on a parameter as well:
// "A part-select operand shall be used to reference a group of adjacent bits in
// a vector net, vector variable, packed array, packed structure, or parameter."
// Indices 8 through 5 of `[8:1] P` are the top four bits of 8'b1010_0101, so
// P[8:5] is 4'b1010. Taking the two indices as distances from the least
// significant end selects one place lower and answers 4'b0101 instead -- the
// same four bits shifted, which is why the pattern is chosen so the two are
// different values rather than a palindrome.
TEST(SelectElaboration, ParameterPartSelectIsAddressedOverItsDeclaredRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [8:1] P = 8'b1010_0101;\n"
      "  localparam Q = P[8:5];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* q = FindParam(design, "m", "Q");
  ASSERT_NE(q, nullptr);
  EXPECT_TRUE(q->is_resolved);
  EXPECT_EQ(q->resolved_value, 0b1010);
}

// An ascending declaration, where the direction of the range decides the answer
// and not just its offset. §11.5.1 reads `logic [0:31] b_vect; b_vect[0 +: 8]`
// as `b_vect[0:7]`, so the right-hand bound of a range is its least significant
// end whichever way the range runs: in `[1:8] R` index 1 is the most
// significant bit. R holds 8'b1010_0101, whose most significant bit is 1.
TEST(SelectElaboration, ParameterBitSelectOverAnAscendingDeclaredRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [1:8] R = 8'b1010_0101;\n"
      "  localparam S = R[1];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* s = FindParam(design, "m", "S");
  ASSERT_NE(s, nullptr);
  EXPECT_TRUE(s->is_resolved);
  EXPECT_EQ(s->resolved_value, 1);
}

// A bound written as an earlier parameter rather than a literal. The two bounds
// are folded where the declaration is elaborated, against the parameters
// already in scope, so `[HI:1]` addresses the same bits `[8:1]` does.
TEST(SelectElaboration, ParameterDeclaredRangeBoundMayBeAParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int HI = 8;\n"
      "  localparam logic [HI:1] V = 8'b1010_0101;\n"
      "  localparam W = V[HI];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* w = FindParam(design, "m", "W");
  ASSERT_NE(w, nullptr);
  EXPECT_TRUE(w->is_resolved);
  EXPECT_EQ(w->resolved_value, 1);
}

// The ordinary spelling, which this rule leaves alone. A declaration ending at
// 0 makes an index and a distance from the least significant end the same
// number, so this test cannot show on its own that the declaration is consulted
// -- it is here to pin that the common case still answers what it always did.
TEST(SelectElaboration, ParameterPartSelectOverARangeEndingAtZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [7:0] T = 8'b1010_0101;\n"
      "  localparam U = T[7:4];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* u = FindParam(design, "m", "U");
  ASSERT_NE(u, nullptr);
  EXPECT_TRUE(u->is_resolved);
  EXPECT_EQ(u->resolved_value, 0b1010);
}

// §11.5.1 admits a part-select of a "packed array", and an address supplied to
// a packed array selects one of its inner vectors: `arr[1]` of
// `logic [1:0][0:7] arr` is a vector declared [0:7]. That range counts upward,
// so its more significant bit is the one with the smaller index and [0:3] names
// the first four bits of the selected vector in order.
//
// The two dimensions are deliberately written in opposite directions. The outer
// one counts downward and the inner one upward, so a check that judged the
// range against the outer dimension -- the one the declaration names first, and
// the only one this file's other declarations have -- would answer the wrong
// way round on both of these cases rather than agreeing with them by accident.
TEST(SelectElaboration, AscendingPartSelectOfAnAscendingPackedElementIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [1:0][0:7] arr;\n"
             "  logic [3:0] result;\n"
             "  initial result = arr[1][0:3];\n"
             "endmodule\n"));
}

TEST(SelectElaboration,
     DescendingPartSelectOfAnAscendingPackedElementIsIllegal) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic [1:0][0:7] arr;\n"
             "  logic [3:0] result;\n"
             "  initial result = arr[1][3:0];\n"
             "endmodule\n"));
}

// The twin declaration, whose inner dimension counts downward. The part-select
// rejected just above is the one written in order here, and the one accepted
// just above is the one written backwards.
TEST(SelectElaboration, DescendingPartSelectOfADescendingPackedElementIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [1:0][7:0] darr;\n"
             "  logic [3:0] result;\n"
             "  initial result = darr[1][3:0];\n"
             "endmodule\n"));
}

TEST(SelectElaboration,
     AscendingPartSelectOfADescendingPackedElementIsIllegal) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic [1:0][7:0] darr;\n"
             "  logic [3:0] result;\n"
             "  initial result = darr[1][0:3];\n"
             "endmodule\n"));
}
