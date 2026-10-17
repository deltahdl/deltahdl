#include <gtest/gtest.h>

#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// A design whose one continuous assignment's right side is the expression a
// case is about.
class AssignedExpressionsOfARun : public VpiDesignRun {
 protected:
  // The right side of the top's continuous assignment.
  static vpiHandle Rhs() {
    vpiHandle it = vpi_iterate(vpiContAssign, By("top"));
    if (it == nullptr) return nullptr;
    return vpi_handle(vpiRhs, vpi_scan(it));
  }

  // The integer value of an expression object, -1 where none is written.
  static int IntOf(vpiHandle expr) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = -1;
    vpi_get_value(expr, &value);
    return value.value.integer;
  }

  // The operands of an operation, in order.
  static std::vector<vpiHandle> OperandsOf(vpiHandle op) {
    std::vector<vpiHandle> operands;
    vpiHandle it = vpi_iterate(vpiOperand, op);
    if (it == nullptr) return operands;
    while (vpiHandle operand = vpi_scan(it)) operands.push_back(operand);
    return operands;
  }

  // The integer values of `exprs`, in order.
  static std::vector<int> ValuesOf(const std::vector<vpiHandle>& exprs) {
    std::vector<int> values;
    values.reserve(exprs.size());
    for (vpiHandle expr : exprs) values.push_back(IntOf(expr));
    return values;
  }
};

// Detail 9: a part select is a constant select when its parent is, the parent
// has static bounds and both bounds are elaboration-time constants.
TEST_F(AssignedExpressionsOfARun, APartSelectWithConstantBoundsIsConstant) {
  Run("module top; logic [7:0] r; wire [3:0] w; assign w = r[3:0];\n"
      "endmodule\n");
  vpiHandle select = Rhs();
  ASSERT_NE(select, nullptr);
  ASSERT_EQ(vpi_get(vpiType, select), vpiPartSelect);
  EXPECT_EQ(vpi_get(vpiConstantSelect, select), 1);
}

// Detail 9: an indexed part select whose base varies is not.
TEST_F(AssignedExpressionsOfARun, AnIndexedPartSelectWithAVaryingBaseIsNot) {
  Run("module top; logic [7:0] r; logic [2:0] i; wire [3:0] w;\n"
      "  assign w = r[i+:4];\n"
      "endmodule\n");
  vpiHandle select = Rhs();
  ASSERT_NE(select, nullptr);
  ASSERT_EQ(vpi_get(vpiType, select), vpiIndexedPartSelect);
  EXPECT_EQ(vpi_get(vpiConstantSelect, select), 0);
}

// Details 3 and 5: a cast is a unary operation whose typespec is the type it
// casts to, a built-in type a keyword names...
TEST_F(AssignedExpressionsOfARun, ACastToAKeywordTypeReachesItsTypespec) {
  Run("module top; logic [7:0] r; wire [31:0] w; assign w = int'(r);\n"
      "endmodule\n");
  vpiHandle cast = Rhs();
  ASSERT_NE(cast, nullptr);
  ASSERT_EQ(vpi_get(vpiOpType, cast), vpiCastOp);
  vpiHandle typespec = vpi_handle(vpiTypespec, cast);
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiIntTypespec);
}

// ...or a typedef the module declares.
TEST_F(AssignedExpressionsOfARun, ACastToATypedefReachesItsTypespec) {
  Run("module top; typedef logic [3:0] nib_t; logic [7:0] r; wire [3:0] w;\n"
      "  assign w = nib_t'(r);\n"
      "endmodule\n");
  vpiHandle cast = Rhs();
  ASSERT_NE(cast, nullptr);
  ASSERT_EQ(vpi_get(vpiOpType, cast), vpiCastOp);
  vpiHandle typedefs = vpi_iterate(vpiTypedef, By("top"));
  ASSERT_NE(typedefs, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_scan(typedefs)), "nib_t");
  vpi_release_handle(typedefs);
  vpiHandle typespec = vpi_handle(vpiTypespec, cast);
  ASSERT_NE(typespec, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, typespec), "nib_t");
}

// The typespec a cast relates to, null for none.
vpiHandle CastTypespec(vpiHandle cast) {
  if (cast == nullptr || vpi_get(vpiOpType, cast) != vpiCastOp) return nullptr;
  return vpi_handle(vpiTypespec, cast);
}

// ...or, for a size cast, a vector keeping the operand's 2-state nature
// (§6.24.1)...
TEST_F(AssignedExpressionsOfARun, ASizeCastOfATwoStateOperandIsABitVector) {
  Run("module top; int i; wire [7:0] w; assign w = 8'(i); endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiBitTypespec);
}

// ...or its 4-state nature...
TEST_F(AssignedExpressionsOfARun, ASizeCastOfAFourStateOperandIsALogicVector) {
  Run("module top; logic [3:0] r; wire [7:0] w; assign w = 8'(r);\n"
      "endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiLogicTypespec);
}

// ...an operation's being 2-state where every operand is (§11.8.1)...
TEST_F(AssignedExpressionsOfARun, ASizeCastOfATwoStateOperationIsABitVector) {
  Run("module top; int i, j; wire [7:0] w; assign w = 8'(i + j);\n"
      "endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiBitTypespec);
}

// ...and 4-state where one is not...
TEST_F(AssignedExpressionsOfARun, ASizeCastOfAMixedOperationIsALogicVector) {
  Run("module top; int i; logic [3:0] r; wire [7:0] w;\n"
      "  assign w = 8'(i + r);\n"
      "endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiLogicTypespec);
}

// ...as wide as its size expression's value, a parameter's included...
TEST_F(AssignedExpressionsOfARun, ASizeCastIsAsWideAsItsSizeExpression) {
  Run("module top; localparam W = 6; logic [3:0] r; wire [7:0] w;\n"
      "  assign w = W'(r);\n"
      "endmodule\n");
  ASSERT_NE(CastTypespec(Rhs()), nullptr);
  EXPECT_EQ(vpi_get(vpiSize, Rhs()), 6);
}

// ...or, for a signing cast, the operand's type of the signedness it names...
TEST_F(AssignedExpressionsOfARun, ASigningCastIsTheOperandsTypeSigned) {
  Run("module top; logic [7:0] r; wire [7:0] w; assign w = signed'(r);\n"
      "endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiLogicTypespec);
  EXPECT_EQ(vpi_get(vpiSigned, typespec), 1);
}

// ...unsigned where it names that...
TEST_F(AssignedExpressionsOfARun, AnUnsigningCastIsTheOperandsTypeUnsigned) {
  Run("module top; int i; wire [31:0] w; assign w = unsigned'(i);\n"
      "endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiIntTypespec);
  EXPECT_EQ(vpi_get(vpiSigned, typespec), 0);
}

// ...or, for a const cast, the operand's own type.
TEST_F(AssignedExpressionsOfARun, AConstCastIsTheOperandsType) {
  Run("module top; int i; wire [31:0] w; assign w = const'(i); endmodule\n");
  vpiHandle typespec = CastTypespec(Rhs());
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiIntTypespec);
}

// Every expression has vpiSize, an operation's being its self-determined
// width (§11.6.1): a bitwise and is as wide as its wider operand, and an
// equality is one bit.
TEST_F(AssignedExpressionsOfARun, AnOperationIsSizedByItsSelfDeterminedWidth) {
  Run("module top; wire [7:0] a; wire [5:0] b; wire [7:0] y;\n"
      "  assign y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(Rhs(), nullptr);
  EXPECT_EQ(vpi_get(vpiSize, Rhs()), 8);
}

TEST_F(AssignedExpressionsOfARun, AnEqualityIsOneBit) {
  Run("module top; wire [7:0] a, b; wire y; assign y = a == b; endmodule\n");
  ASSERT_NE(Rhs(), nullptr);
  EXPECT_EQ(vpi_get(vpiSize, Rhs()), 1);
}

// A part select is as wide as its bounds span, and an indexed part select as
// its width.
TEST_F(AssignedExpressionsOfARun, PartSelectsAreSizedByTheirRanges) {
  Run("module top; wire [7:0] a; wire [2:0] y; assign y = a[6:4];\n"
      "endmodule\n");
  ASSERT_NE(Rhs(), nullptr);
  EXPECT_EQ(vpi_get(vpiSize, Rhs()), 3);
}

TEST_F(AssignedExpressionsOfARun, AnIndexedPartSelectIsSizedByItsWidth) {
  Run("module top; logic [7:0] r; logic [2:0] i; wire [4:0] w;\n"
      "  assign w = r[i+:5];\n"
      "endmodule\n");
  ASSERT_NE(Rhs(), nullptr);
  EXPECT_EQ(vpi_get(vpiSize, Rhs()), 5);
}

// A bit select and a part select hold no storage of their own; each reads the
// bits it selects out of its parent's value.
TEST_F(AssignedExpressionsOfARun, ABitSelectReadsItsBit) {
  Run("module top; integer n = 5; wire y; assign y = n[2]; endmodule\n");
  ASSERT_NE(Rhs(), nullptr);
  ASSERT_EQ(vpi_get(vpiType, Rhs()), vpiBitSelect);
  EXPECT_EQ(IntOf(Rhs()), 1);
}

TEST_F(AssignedExpressionsOfARun, APartSelectReadsItsBits) {
  Run("module top; logic [7:0] r = 8'hA5; wire [3:0] y; assign y = r[7:4];\n"
      "endmodule\n");
  ASSERT_NE(Rhs(), nullptr);
  ASSERT_EQ(vpi_get(vpiType, Rhs()), vpiPartSelect);
  EXPECT_EQ(IntOf(Rhs()), 0xA);
}

// Detail 6: a keyed pattern nested in a keyed pattern keeps its place, laid
// out positionally by the subarray it fills, nesting preserved. §10.8 lets no
// untyped pattern be a default key's value, so each subarray is keyed.
TEST_F(AssignedExpressionsOfARun, ANestedKeyedPatternKeepsItsPlace) {
  Run("module top; logic [1:0] a [0:1][0:1];\n"
      "  assign a = '{0: '{1: 2'd1, default: 2'd0}, 1: '{default: 2'd3}};\n"
      "endmodule\n");
  vpiHandle pattern = Rhs();
  ASSERT_NE(pattern, nullptr);
  ASSERT_EQ(vpi_get(vpiOpType, pattern), vpiAssignmentPatternOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(pattern);
  ASSERT_EQ(kOperands.size(), 2U);
  EXPECT_EQ(vpi_get(vpiOpType, kOperands[0]), vpiAssignmentPatternOp);
  EXPECT_EQ(ValuesOf(OperandsOf(kOperands[0])), (std::vector<int>{0, 1}));
  EXPECT_EQ(vpi_get(vpiOpType, kOperands[1]), vpiAssignmentPatternOp);
  EXPECT_EQ(ValuesOf(OperandsOf(kOperands[1])), (std::vector<int>{3, 3}));
}

// Detail 10 with Table 37-1: the parent of r[i+1][3][j+:2] is r[i+1][3], a
// select of one packed element out of the element r[i+1] selects, whose own
// parent is that var select.
TEST_F(AssignedExpressionsOfARun, APartSelectThroughAVarSelectHasItsParent) {
  Run("module top; logic [0:3][7:0] r [1:4]; int i, j; wire [1:0] w;\n"
      "  assign w = r[i+1][3][j+:2];\n"
      "endmodule\n");
  vpiHandle select = Rhs();
  ASSERT_NE(select, nullptr);
  ASSERT_EQ(vpi_get(vpiType, select), vpiIndexedPartSelect);
  vpiHandle parent = vpi_handle(vpiParent, select);
  ASSERT_NE(parent, nullptr);
  EXPECT_EQ(vpi_get(vpiType, parent), vpiBitSelect);
  EXPECT_EQ(vpi_get(vpiSize, parent), 8);
  vpiHandle element = vpi_handle(vpiParent, parent);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(vpi_get(vpiType, element), vpiVarSelect);
}

}  // namespace
}  // namespace delta
