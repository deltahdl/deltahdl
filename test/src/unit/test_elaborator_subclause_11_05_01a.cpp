#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
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

TEST(SelectElaboration, ReversedPartSelectOfANonZeroBasedVectorNames11_5_1) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic [7:4] v;\n"
      "  logic [3:0] result;\n"
      "  initial result = v[4:7];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more", 4,
                            "11.5.1"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            4, "11.5.1"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            4, "11.5.1"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "indexed part-select width must be a constant expression", 5, "11.5.1"));
}

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "indexed part-select width must be a positive constant", 4, "11.5.1"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 4,
                            "6.12"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select of a real variable is illegal", 4,
                            "6.12"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "non-indexed part-select bounds shall be constant",
                            5, "11.5.1"));
}

TEST(SelectElaboration, PartSelectBoundsMayQueryASignal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [3:0] b;\n"
      "  logic [7:0] m [4];\n"
      "  logic [15:0] data;\n"
      "  logic [3:0] y, z;\n"
      "  assign y = data[$bits(b)-1:0];\n"
      "  assign z = data[$size(m)+3:$size(m)];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SelectElaboration, PartSelectBoundReadingASignalBesideAQueryIsNot) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [3:0] b;\n"
      "  integer w;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] y, z;\n"
      "  assign y = data[$bits(b)+w:0];\n"
      "  assign z = data[$clog2(w):0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "non-indexed part-select bounds shall be constant",
                            6, "11.5.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "non-indexed part-select bounds shall be constant",
                            7, "11.5.1"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more", 4,
                            "11.5.1"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real parameter is illegal", 4,
                            "11.5.1"));
}

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

TEST(SelectElaboration, UnpackedStructBitSelectIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct { logic [3:0] hi; logic [3:0] lo; } s;\n"
      "  logic b;\n"
      "  initial b = s[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            4, "11.5.1"));
}

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

TEST(SelectElaboration, ShortrealVariableBitSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  shortreal r;\n"
      "  logic y;\n"
      "  assign y = r[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 4,
                            "6.12"));
}

TEST(SelectElaboration, RealtimeVariableBitSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  realtime r;\n"
      "  logic y;\n"
      "  assign y = r[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 4,
                            "6.12"));
}

TEST(SelectElaboration, AscendingDeclReversedPartSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [0:15] data;\n"
      "  logic [7:0] y;\n"
      "  assign y = data[7:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more", 4,
                            "11.5.1"));
}

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
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic [1:0][0:7] arr;\n"
      "  logic [3:0] result;\n"
      "  initial result = arr[1][3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more", 4,
                            "11.5.1"));
}

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
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic [1:0][7:0] darr;\n"
      "  logic [3:0] result;\n"
      "  initial result = darr[1][0:3];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more", 4,
                            "11.5.1"));
}

TEST(RealSelect, PartSelectOfARealNamesPartSelect) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real a;\n"
      "  wire [3:0] b;\n"
      "  assign b = a[3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select of a real variable is illegal", 4,
                            "6.12"));
}

TEST(RealSelect, IndexedPlusPartSelectOfARealNamesPartSelect) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real a;\n"
      "  wire [3:0] b;\n"
      "  assign b = a[0 +: 4];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select of a real variable is illegal", 4,
                            "6.12"));
}

TEST(RealSelect, IndexedMinusPartSelectOfARealNamesPartSelect) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real a;\n"
      "  wire [3:0] b;\n"
      "  assign b = a[3 -: 4];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select of a real variable is illegal", 4,
                            "6.12"));
}

TEST(RealSelect, BitSelectOfARealStillNamesBitSelect) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real a;\n"
      "  wire b;\n"
      "  assign b = a[2];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 4,
                            "6.12"));
}

TEST(RealSelect, SelectOfARealDrawsOneReport) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real a;\n"
      "  wire b;\n"
      "  assign b = a[2];\n"
      "endmodule\n",
      f);
  int errors = 0;
  std::string recorded;
  for (const auto& diag : f.diag.Diagnostics()) {
    if (diag.severity != DiagSeverity::kError) continue;
    ++errors;
    recorded += "\n  ";
    recorded += diag.message;
  }
  EXPECT_EQ(errors, 1) << "one select of a real variable drew these errors:"
                       << recorded;
}

TEST(RealSelect, SelectOfARealInAProceduralStatementNamesTheRealRule) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real a;\n"
      "  int b;\n"
      "  always @* b = a[2];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 4,
                            "6.12"));
}

TEST(RealSelect, ElementSelectOfAnUnpackedArrayOfRealsIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  initial v = arr[i];\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealSelect, ElementSelectOfAnUnpackedArrayOfRealsAsATargetIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  initial arr[i] = 4.0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealSelect, ContinuousAssignFromAnUnpackedArrayOfRealsIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  assign v = arr[0];\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealSelect, BitSelectOfARealParameterNamesTheRealRule) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter real P = 1.5;\n"
      "  wire y;\n"
      "  assign y = P[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real parameter is illegal", 4,
                            "11.5.1"));
}

TEST(RealSelect, PartSelectOfARealParameterNamesPartSelect) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter real P = 1.5;\n"
      "  wire [3:0] y;\n"
      "  assign y = P[3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select of a real parameter is illegal", 4,
                            "11.5.1"));
}

TEST(RealSelect, IndexedPartSelectOfARealParameterNamesPartSelect) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter real P = 1.5;\n"
      "  wire [3:0] y;\n"
      "  assign y = P[0 +: 4];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select of a real parameter is illegal", 4,
                            "11.5.1"));
}

TEST(RealSelect, SelectOfARealParameterDrawsOneReport) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  parameter real P = 1.5;\n"
      "  wire y;\n"
      "  assign y = P[0];\n"
      "endmodule\n",
      f);
  int errors = 0;
  std::string recorded;
  for (const auto& diag : f.diag.Diagnostics()) {
    if (diag.severity != DiagSeverity::kError) continue;
    ++errors;
    recorded += "\n  ";
    recorded += diag.message;
  }
  EXPECT_EQ(errors, 1) << "one select of a real parameter drew these errors:"
                       << recorded;
}

TEST(RealSelect, BitSelectOfAScalarStillNamesTheScalarRule) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic x;\n"
      "  wire y;\n"
      "  assign y = x[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            4, "11.5.1"));
}
