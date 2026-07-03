#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(OperatorElaboration, LogicalEqualityElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (8'd5 == 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, LogicalInequalityElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (8'd5 != 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryCaseEqElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (8'd5 === 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryCaseNeqElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (8'd5 !== 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(EqualityOperatorElaboration, AlwaysCombEqualityCheck) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic y;\n"
      "  always_comb y = (a == b);\n"
      "  initial begin\n"
      "    a = 8'h42;\n"
      "    b = 8'h42;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);

  EXPECT_EQ(y->value.ToUint64(), 1u);
}

TEST(EqualityOperatorElaboration, BlockingAssignComparisonOps) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b;\n"
      "  int r_eq, r_ne, r_lt, r_gt, r_le, r_ge;\n"
      "  initial begin\n"
      "    a = 10;\n"
      "    b = 20;\n"
      "    r_eq = (a == b);\n"
      "    r_ne = (a != b);\n"
      "    r_lt = (a < b);\n"
      "    r_gt = (a > b);\n"
      "    r_le = (a <= b);\n"
      "    r_ge = (a >= b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r_eq = f.ctx.FindVariable("r_eq");
  auto* r_ne = f.ctx.FindVariable("r_ne");
  auto* r_lt = f.ctx.FindVariable("r_lt");
  auto* r_gt = f.ctx.FindVariable("r_gt");
  auto* r_le = f.ctx.FindVariable("r_le");
  auto* r_ge = f.ctx.FindVariable("r_ge");
  ASSERT_NE(r_eq, nullptr);
  ASSERT_NE(r_ne, nullptr);
  ASSERT_NE(r_lt, nullptr);
  ASSERT_NE(r_gt, nullptr);
  ASSERT_NE(r_le, nullptr);
  ASSERT_NE(r_ge, nullptr);
  EXPECT_EQ(r_eq->value.ToUint64(), 0u);
  EXPECT_EQ(r_ne->value.ToUint64(), 1u);
  EXPECT_EQ(r_lt->value.ToUint64(), 1u);
  EXPECT_EQ(r_gt->value.ToUint64(), 0u);
  EXPECT_EQ(r_le->value.ToUint64(), 1u);
  EXPECT_EQ(r_ge->value.ToUint64(), 0u);
}

TEST(OperatorElaboration, ChandleEqualityWithNullElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  chandle h;\n"
      "  logic r;\n"
      "  initial r = (h == null);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, ChandleInequalityWithNullElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  chandle h;\n"
      "  logic r;\n"
      "  initial r = (h != null);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.5: comparing a class handle with the literal null using the logical
// equality operator is a legal operation, so elaboration reports no error.
TEST(OperatorElaboration, ClassHandleEqualityWithNullElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C c;\n"
      "  logic r;\n"
      "  initial r = (c == null);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.5: the rule permits a class-handle comparison when one operand is
// assignment compatible with the other. A base handle and a handle of a class
// derived from it satisfy that requirement, and case equality (===) is one of
// the permitted operators, so this comparison elaborates cleanly.
TEST(OperatorElaboration, ClassHandleCaseEqualityCompatibleElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Base; endclass\n"
      "class Derived extends Base; endclass\n"
      "module m;\n"
      "  Base b;\n"
      "  Derived d;\n"
      "  logic r;\n"
      "  initial r = (b === d);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.5: the class-handle comparison is legal only when one operand is
// assignment compatible with the other. Two handles of unrelated classes are
// not, so the equality comparison is rejected. This is the discriminating
// negative for the compatibility requirement above.
TEST(OperatorElaboration, ClassHandleEqualityIncompatibleRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class A; endclass\n"
      "class B; endclass\n"
      "module m;\n"
      "  A a;\n"
      "  B b;\n"
      "  logic r;\n"
      "  initial r = (a == b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §11.4.5: case equality (===) is one of the operators the rule permits between
// a chandle and the literal null, so this comparison elaborates without error.
// Complements the ==/!= chandle-null cases with the case-equality operator
// form.
TEST(OperatorElaboration, ChandleCaseEqualityWithNullElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  chandle h;\n"
      "  logic r;\n"
      "  initial r = (h === null);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.5: two handles of the same class type are trivially assignment
// compatible, so a logical-equality (==) comparison between them is a legal
// operation and elaborates cleanly. Covers the == operator on two class handles
// (the base/derived case above uses ===).
TEST(OperatorElaboration, ClassHandleEqualitySameTypeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  C b;\n"
      "  logic r;\n"
      "  initial r = (a == b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
