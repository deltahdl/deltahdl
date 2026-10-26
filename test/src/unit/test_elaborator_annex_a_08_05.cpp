#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {}

TEST(LvalueElaboration, NetLvalueSimpleContAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  assign a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LvalueElaboration, NetLvalueBitSelectContAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [7:0] a;\n"
      "  wire b;\n"
      "  assign a[3] = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LvalueElaboration, NetLvalueConcatContAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [3:0] a, b;\n"
      "  wire [7:0] c;\n"
      "  assign {a, b} = c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LvalueElaboration, VarLvalueSimpleProceduralAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LvalueElaboration, VarLvalueBitSelectProcedural) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x[3] = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LvalueElaboration, VarLvaluePartSelectProcedural) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x[7:4] = 4'hF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LvalueElaboration, VarLvalueConcatProcedural) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] c;\n"
      "  initial {a, b} = c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LvalueElaboration, VarLvalueMemberAccessProcedural) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  initial p.hi = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LvalueElaboration, VarLvalueNonblockingElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x <= 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LvalueElaboration, VarLvalueStreamingConcatElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] a, b;\n"
      "  initial {>> {a}} = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LvalueElaboration, NonrangeVarLvalueElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LvalueElaboration, NetLvaluePartSelectContAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [7:0] a;\n"
      "  wire [3:0] b;\n"
      "  assign a[7:4] = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LvalueElaboration, VarLvalueIndexedPartSelectProcedural) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] x;\n"
      "  initial x[4+:4] = 4'hF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LvalueElaboration, VarLvalueNestedConcatProcedural) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c, d;\n"
      "  initial {{a, b}, {c, d}} = 4'hF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LvalueElaboration, VarLvalueHierarchicalMemberProcedural) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] x; } inner_t;\n"
      "  typedef struct packed { inner_t sub; } outer_t;\n"
      "  outer_t o;\n"
      "  initial o.sub.x = 8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LvalueElaboration, VarLvalueArrayElementProcedural) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [4];\n"
      "  initial arr[2] = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LvalueElaboration, VarLvalueMemberAccessWithBitSelect) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  initial p.hi[3] = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LvalueElaboration, VarLvalueSingleElementConcatProcedural) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  initial {a} = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LvalueElaboration, VarLvalueAssignmentPatternProcedural) {
  // variable_lvalue's assignment_pattern_variable_lvalue alternative: the
  // positional pattern `'{a, b}` stands as the procedural-assignment target.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  initial '{a, b} = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LvalueElaboration, NetLvalueAssignmentPatternContAssign) {
  // net_lvalue's assignment_pattern_net_lvalue alternative: the pattern `'{x,
  // y}` stands as a continuous-assignment target over nets.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [3:0] x, y;\n"
      "  assign '{x, y} = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A.10 footnote 51 (printed page 1218), on A.8.5's variable_lvalue, holds
// every select in the variable_lvalue a sequence match item assigns to a
// constant_select. A module variable and a local variable are no constants,
// and a literal and a parameter are.
TEST(LvalueElaboration, MatchItemTargetSelectThatIsNotConstantIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter int P = 2;\n"
      "  logic clk, a, b;\n"
      "  int k;\n"
      "  property p;\n"
      "    logic [7:0] v;\n"
      "    @(posedge clk) (a, v[k] = b) |-> 1;\n"
      "  endproperty\n"
      "  property q;\n"
      "    logic [7:0] v;\n"
      "    @(posedge clk) (a, v[1] = b, v[P] = b) |-> 1;\n"
      "  endproperty\n"
      "  property r;\n"
      "    logic [7:0] v;\n"
      "    int i;\n"
      "    @(posedge clk) (a, i = 0, v[i] = b) |-> 1;\n"
      "  endproperty\n"
      "  assert property (p);\n"
      "  assert property (q);\n"
      "  assert property (r);\n"
      "endmodule\n",
      f);
  constexpr std::string_view kMessage =
      "a sequence match item assigns through a select that is not constant";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 7, "A.8.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 16, "A.8.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

// A.10 footnote 52 (printed page 1218), on A.8.5's variable_lvalue, nests no
// streaming concatenation within another variable_lvalue, and a streaming
// concatenation written as the target of a procedural assignment, of an
// assignment within an expression or of a continuous assignment is one. A
// streaming concatenation read as a source may nest another, as §11.4.14.2's
// own example does.
TEST(LvalueElaboration, StreamNestedInAStreamTargetIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] v, n, x, y, p, q;\n"
      "  initial {>>{v, {<<{n}}}} = {x, x};\n"
      "  initial y = ({>>{v, {<<{n}}}} = {x, x});\n"
      "  assign {>>{p, {<<{q}}}} = {x, x};\n"
      "  initial {>>{v, n}} = {x, x};\n"
      "  initial y = {<<2{{<<{4'b1101}}}};\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 4u, 5u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a streaming concatenation written as a target "
                              "holds no streaming concatenation among its "
                              "stream expressions",
                              line, "A.8.5"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}
