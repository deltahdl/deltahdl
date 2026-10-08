#include <gtest/gtest.h>

#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.58 Simple expressions: the VPI object model for a simple expression - a
// reference (net, variable, ref obj, parameter, spec param) or a select of one
// (var select, bit select). The name/full-name strings and the value relation
// are the generic naming machinery carried by §38.11; the subclause's own
// normative rules are its three numbered Details - the content of the vpiUse
// relation for a vector and for a bit-select, and the vpiConstantSelect
// property of a bit-select. The vpiParent and vpiIndex relations the figure
// draws from a bit select are this clause's too, because a relation named for
// the edge reaches nothing without a rule that says what it reaches. These
// tests observe the production code that applies all of those.

// Detail 1: for a vector simple expression, the vpiUse relation reaches every
// use of the vector itself together with every use of any of the vector's
// part-selects or bit-selects. A candidate use is therefore accessed when it
// references the vector or either kind of derived select, and only an
// unrelated use is excluded.
TEST(SimpleExpressionModel, VectorUseReachesVectorPartSelectsAndBitSelects) {
  // A use of the vector itself is accessed.
  EXPECT_TRUE(VpiSimpleExprVectorUseAccessesUse(
      /*references_vector=*/true, /*references_part_select_of_vector=*/false,
      /*references_bit_select_of_vector=*/false));
  // A use of one of the vector's part-selects is accessed.
  EXPECT_TRUE(VpiSimpleExprVectorUseAccessesUse(false, true, false));
  // A use of one of the vector's bit-selects is accessed.
  EXPECT_TRUE(VpiSimpleExprVectorUseAccessesUse(false, false, true));
  // A use that references none of those is not accessed.
  EXPECT_FALSE(VpiSimpleExprVectorUseAccessesUse(false, false, false));
}

// Detail 2: for a bit-select, the vpiUse relation reaches every specific use of
// that bit, every use of the parent vector, and every part-select of the parent
// that contains the bit. Each of those three independently makes a use
// accessed, and a use that matches none of them is excluded.
TEST(SimpleExpressionModel, BitSelectUseReachesBitParentAndContainingSelect) {
  // A specific use of the bit itself is accessed.
  EXPECT_TRUE(VpiSimpleExprBitSelectUseAccessesUse(
      /*references_this_bit=*/true, /*references_parent_vector=*/false,
      /*references_part_select_containing_bit=*/false));
  // A use of the parent vector is accessed.
  EXPECT_TRUE(VpiSimpleExprBitSelectUseAccessesUse(false, true, false));
  // A use of a part-select of the parent that contains the bit is accessed.
  EXPECT_TRUE(VpiSimpleExprBitSelectUseAccessesUse(false, false, true));
  // A use matching none of the three is not accessed. (For example, a
  // part-select of the parent that does not contain this bit.)
  EXPECT_FALSE(VpiSimpleExprBitSelectUseAccessesUse(false, false, false));
}

// Detail 3: vpiConstantSelect of a bit-select is TRUE only when both conditions
// hold - every associated index expression is an elaboration-time constant and
// vpiConstantSelect is itself TRUE for the bit-select's parent. When both hold
// the property is TRUE, and dropping either condition makes it FALSE.
TEST(SimpleExpressionModel, BitSelectConstantSelectRequiresBothConditions) {
  EXPECT_TRUE(VpiSimpleExprBitSelectConstantSelect(
      /*all_indices_constant=*/true, /*parent_constant_select=*/true));

  // An index expression is not an elaboration-time constant -> FALSE.
  EXPECT_FALSE(VpiSimpleExprBitSelectConstantSelect(false, true));

  // The parent is not itself a constant select -> FALSE.
  EXPECT_FALSE(VpiSimpleExprBitSelectConstantSelect(true, false));

  // Neither condition holds -> FALSE.
  EXPECT_FALSE(VpiSimpleExprBitSelectConstantSelect(false, false));
}

// Detail 3 through the figure's own reading. §37.4.2 reads "bool:
// vpiConstantSelect" with vpi_get(), so the property is answered on a bit
// select object rather than from booleans a caller worked out; the rule was
// applied by a helper nothing called, so the property read 0 whatever the
// select was.
class BitSelectObject : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    vector_.type = vpiIntegerVar;
    index_.type = vpiConstant;
    select_.type = vpiBitSelect;
    select_.parent = &vector_;
    select_.children = {&index_};
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  std::vector<vpiHandle> ScanAll(vpiHandle it) {
    std::vector<vpiHandle> seen;
    if (it == nullptr) return seen;
    while (vpiHandle h = vpi_scan(it)) seen.push_back(h);
    return seen;
  }

  VpiObject vector_;
  VpiObject index_;
  VpiObject select_;
  VpiContext ctx_;
};

// Detail 3, both conditions met: a constant index into a vector of static
// lifetime.
TEST_F(BitSelectObject, AConstantIndexIntoAStaticVectorIsAConstantSelect) {
  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&select_)), 1);
}

// Detail 3, first condition: an index that is not an elaboration-time constant.
TEST_F(BitSelectObject, ANonConstantIndexMakesTheSelectNonConstant) {
  index_.type = vpiOperation;

  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&select_)), 0);
}

// Detail 3, second condition: the prefix has to be a constant select itself,
// and a vector of automatic lifetime is not one.
TEST_F(BitSelectObject, AnAutomaticPrefixMakesTheSelectNonConstant) {
  vector_.automatic = true;

  EXPECT_EQ(vpi_get(vpiConstantSelect, VpiHandleOf(&select_)), 0);
}

// The figure's vpiParent edge, drawn from the bit select to the class grouping
// a var select, an integer var, a time var, a parameter and a spec param.
// vpiParent is a tag no object's type is, so the traversal the relation fell
// through to reached the vector from none of its bit-selects.
TEST_F(BitSelectObject, ParentReachesTheVectorSelectedInto) {
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, VpiHandleOf(&select_))),
            &vector_);
}

// The figure's vpiIndex edge, drawn from the bit select to expr and walked with
// vpi_iterate()/vpi_scan() (§37.4.3). It was recognized for no reference object
// of this kind, so the index a select was written with was reachable from it by
// nothing.
TEST_F(BitSelectObject, IndexReachesTheSelectsIndexExpression) {
  std::vector<vpiHandle> seen =
      ScanAll(vpi_iterate(vpiIndex, VpiHandleOf(&select_)));
  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &index_);
}

// A design whose one continuous assignment's right side is a bit select, run
// with a PLI application registered.
class BitSelectsOfARun : public VpiDesignRun {
 protected:
  // The integer value of an object.
  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }

  // Puts the integer `integer` to an object, with no delay.
  static void PutInt(vpiHandle obj, int integer) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = integer;
    vpi_put_value(obj, &value, nullptr, vpiNoDelay);
  }

  // The right side of the top's continuous assignment.
  static vpiHandle Rhs() {
    vpiHandle it =
        vpi_iterate(vpiContAssign, vpi_handle_by_name(VpiText("top"), nullptr));
    if (it == nullptr) return nullptr;
    return vpi_handle(vpiRhs, vpi_scan(it));
  }
};

constexpr const char* kIntegerBit =
    "module top; integer i = 8; wire y; assign y = i[3]; endmodule\n";

// §37.58: a select of one bit of an integer var is a bit select...
TEST_F(BitSelectsOfARun, ABitOfAnIntegerIsABitSelect) {
  Run(kIntegerBit);
  EXPECT_EQ(vpi_get(vpiType, Rhs()), vpiBitSelect);
}

// ...whose parent is the variable...
TEST_F(BitSelectsOfARun, ABitSelectsParentIsTheVariable) {
  Run(kIntegerBit);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiParent, Rhs())), "i");
}

// ...and whose index is the expression the source wrote.
TEST_F(BitSelectsOfARun, ABitSelectsIndexIsTheWrittenIndex) {
  Run(kIntegerBit);
  EXPECT_EQ(IntOf(vpi_handle(vpiIndex, Rhs())), 3);
}

// A select of one bit of a vector net is no bit select: it is that net's bit
// (§37.16), the object the index reaches. The net is declared without an
// assignment, which would be the top's first continuous assignment.
TEST_F(BitSelectsOfARun, ABitOfANetIsTheNetsBit) {
  Run("module top; wire [7:0] a; wire y; assign y = a[3]; endmodule\n");
  EXPECT_EQ(Rhs(), vpi_handle_by_index(
                       vpi_handle_by_name(VpiText("top.a"), nullptr), 3));
}

constexpr const char* kVaryingNetBit =
    "module top; wire [7:0] a; integer i = 2; wire y; assign y = a[i];\n"
    "endmodule\n";

// A bit of a vector net selected by an index that is not a constant is still
// one of the net's bits (§37.16), though which one is not fixed before the
// run...
TEST_F(BitSelectsOfARun, AVaryingBitOfANetIsANetBit) {
  Run(kVaryingNetBit);
  EXPECT_EQ(vpi_get(vpiType, Rhs()), vpiNetBit);
}

// ...whose parent is the net...
TEST_F(BitSelectsOfARun, AVaryingBitsParentIsTheNet) {
  Run(kVaryingNetBit);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiParent, Rhs())), "a");
}

// ...whose index is the expression the source wrote...
TEST_F(BitSelectsOfARun, AVaryingBitsIndexIsTheWrittenIndex) {
  Run(kVaryingNetBit);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiIndex, Rhs())), "i");
}

// ...and which is no constant select (§37.16 detail 23).
TEST_F(BitSelectsOfARun, AVaryingBitIsNoConstantSelect) {
  Run(kVaryingNetBit);
  EXPECT_EQ(vpi_get(vpiConstantSelect, Rhs()), 0);
}

// Of a packed variable it is one of the variable's bits (§37.17).
TEST_F(BitSelectsOfARun, AVaryingBitOfAVariableIsAVarBit) {
  Run("module top; logic [7:0] v; integer i = 2; wire y; assign y = v[i];\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, Rhs()), vpiRegBit);
}

constexpr const char* kVaryingVarBit =
    "module top; logic [7:0] v = 8'b0000_0100; integer i = 2; wire y;\n"
    "assign y = v[i];\n"
    "endmodule\n";

// The value of a varying bit (§37.17, §38.15) is that of the variable's bit
// its index selects when the value is read...
TEST_F(BitSelectsOfARun, AVaryingBitHoldsTheBitItsIndexSelects) {
  Run(kVaryingVarBit);
  EXPECT_EQ(IntOf(Rhs()), 1);
}

// ...so it follows the index from one read to the next...
TEST_F(BitSelectsOfARun, AVaryingBitFollowsItsIndex) {
  Run(kVaryingVarBit);
  PutInt(vpi_handle_by_name(VpiText("top.i"), nullptr), 4);
  EXPECT_EQ(IntOf(Rhs()), 0);
}

// ...and an index naming no bit of a 4-state vector reads x (§11.5.1).
TEST_F(BitSelectsOfARun, AVaryingBitPastTheRangeReadsX) {
  Run(kVaryingVarBit);
  PutInt(vpi_handle_by_name(VpiText("top.i"), nullptr), 9);
  s_vpi_value value = {};
  value.format = vpiScalarVal;
  vpi_get_value(Rhs(), &value);
  EXPECT_EQ(value.value.scalar, vpiX);
}

// A value put to a varying bit is put to the bit its index selects.
TEST_F(BitSelectsOfARun, WritingAVaryingBitWritesTheBitItsIndexSelects) {
  Run(kVaryingVarBit);
  PutInt(vpi_handle_by_name(VpiText("top.i"), nullptr), 0);
  PutInt(Rhs(), 1);
  EXPECT_EQ(IntOf(vpi_handle_by_name(VpiText("top.v"), nullptr)), 5);
}

// A varying bit of a net holds the net's bit its index selects (§37.16). The
// net's own assignment comes second, so the select is the top's first.
TEST_F(BitSelectsOfARun, AVaryingBitOfANetHoldsTheBitItsIndexSelects) {
  Run("module top; wire [7:0] a; integer i = 2; wire y; assign y = a[i];\n"
      "assign a = 8'b0000_0100;\n"
      "endmodule\n");
  EXPECT_EQ(IntOf(Rhs()), 1);
}

// §37.58 with §37.16: a bit reaches its index and the object it is a bit of,
// and through the select relations no other: asked for an expression, a net
// bit resolves to nothing there.
TEST_F(BitSelectObject, ABitResolvesOnlyItsIndexAndParent) {
  VpiObject net;
  net.type = vpiNet;
  VpiObject bit;
  bit.type = vpiNetBit;
  bit.parent = &net;
  VpiHandle out = nullptr;
  EXPECT_FALSE(TryResolveSelectRelation(vpiExpr, &bit, out));
  EXPECT_EQ(out, nullptr);
}

// §37.58 detail 3 read off the object: a null handle and an object that is no
// bit-select are no constant select; a bit-select with no parent is not one
// whatever its indices, children of no expression kind not being indices; and
// a bit-select of a bit-select or of a var select follows its parent's answer.
TEST(BitSelectConstantSelect, ReadOffTheSelectAndItsParent) {
  EXPECT_FALSE(VpiBitSelectConstantSelectOf(nullptr));
  VpiObject ref;
  ref.type = vpiRefObj;
  EXPECT_FALSE(VpiBitSelectConstantSelectOf(&ref));

  VpiObject attribute;
  attribute.type = vpiAttribute;
  VpiObject index;
  index.type = vpiConstant;
  VpiObject orphan;
  orphan.type = vpiBitSelect;
  orphan.children = {&attribute, &index};
  EXPECT_FALSE(VpiBitSelectConstantSelectOf(&orphan));

  VpiObject var;
  var.type = vpiIntegerVar;
  VpiObject inner;
  inner.type = vpiBitSelect;
  inner.parent = &var;
  inner.children = {&index};
  VpiObject outer;
  outer.type = vpiBitSelect;
  outer.parent = &inner;
  outer.children = {&index};
  EXPECT_TRUE(VpiBitSelectConstantSelectOf(&outer));

  VpiObject var_select;
  var_select.type = vpiVarSelect;
  VpiObject of_var_select;
  of_var_select.type = vpiBitSelect;
  of_var_select.parent = &var_select;
  of_var_select.children = {&index};
  EXPECT_EQ(VpiBitSelectConstantSelectOf(&of_var_select),
            VpiVarSelectConstantSelectOf(&var_select));
}
}  // namespace
}  // namespace delta
