#include <gtest/gtest.h>

#include <algorithm>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_simple_expr_uses.h"
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

// Detail 3, first condition: an index that is not an elaboration-time
// constant, an operation reading a variable (§11.2.1).
TEST_F(BitSelectObject, ANonConstantIndexMakesTheSelectNonConstant) {
  VpiObject variable;
  variable.type = vpiIntegerVar;
  index_.type = vpiOperation;
  index_.children = {&variable};

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

// The right-hand sides of the continuous assignments `scope` holds, in the
// order vpiContAssign reaches them.
std::vector<vpiHandle> RightSides(vpiHandle scope) {
  std::vector<vpiHandle> sides;
  vpiHandle it = vpi_iterate(vpiContAssign, scope);
  if (it == nullptr) return sides;
  for (vpiHandle ca = vpi_scan(it); ca != nullptr; ca = vpi_scan(it)) {
    sides.push_back(vpi_handle(vpiRhs, ca));
  }
  return sides;
}

// §37.16 with §11.2.1: an index that is an elaboration-time constant without
// being a literal -- a parameter, or an operation over one -- chooses the
// net's bit its value names, as a literal index does, and so a constant
// select (§37.16 detail 23).
TEST_F(BitSelectsOfARun, AParameterIndexChoosesTheNetsOwnBit) {
  Run("module top; parameter P = 4; wire [7:0] a; wire y, z;\n"
      "assign y = a[P]; assign z = a[P-1];\n"
      "endmodule\n");
  const std::vector<vpiHandle> kSides = RightSides(By("top"));
  ASSERT_EQ(kSides.size(), 2U);
  EXPECT_EQ(kSides[0], vpi_handle_by_index(By("top.a"), 4));
  EXPECT_EQ(kSides[1], vpi_handle_by_index(By("top.a"), 3));
  EXPECT_EQ(vpi_get(vpiConstantSelect, kSides[0]), 1);
}

// ...as does a genvar, a constant in each block instance its loop generates
// (§27.4).
TEST_F(BitSelectsOfARun, AGenvarIndexChoosesTheNetsOwnBit) {
  Run("module top; wire [7:0] a;\n"
      "  for (genvar g = 2; g < 4; g++) begin : gb\n"
      "    wire y; assign y = a[g];\n"
      "  end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kSides = RightSides(By("top.gb[3]"));
  ASSERT_EQ(kSides.size(), 1U);
  EXPECT_EQ(kSides[0], vpi_handle_by_index(By("top.a"), 3));
}

// §37.17 details 2 and 18: into an unpacked array var, such an index chooses
// the element its value names, as a literal index does, and no var select.
TEST_F(BitSelectsOfARun, AParameterIndexChoosesTheArraysElement) {
  Run("module top; parameter P = 1; logic [7:0] arr [0:3]; wire [7:0] y;\n"
      "assign y = arr[P];\n"
      "endmodule\n");
  EXPECT_EQ(Rhs(), vpi_handle_by_index(By("top.arr"), 1));
}

// §37.58 detail 3 with §11.2.1: a bit select of an integer var keeps the index
// it was written with, and is a constant select where that is a parameter or
// an operation over one, and not where it is an operation over a variable.
TEST_F(BitSelectsOfARun, AParameterIndexedBitSelectIsAConstantSelect) {
  Run("module top; parameter P = 4; integer i, k; wire a, b, c;\n"
      "assign a = i[P]; assign b = i[P-1]; assign c = i[k+1];\n"
      "endmodule\n");
  const std::vector<vpiHandle> kSides = RightSides(By("top"));
  ASSERT_EQ(kSides.size(), 3U);
  EXPECT_EQ(vpi_get(vpiType, kSides[0]), vpiBitSelect);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kSides[0]), 1);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kSides[1]), 1);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kSides[2]), 0);
}

// §37.59 detail 9: so is a part select bounded by a parameter, and an indexed
// part select of a parameter width based on a constant, but not one based on
// a variable.
TEST_F(BitSelectsOfARun, AParameterBoundedPartSelectIsAConstantSelect) {
  Run("module top; parameter P = 4; wire [7:0] n; integer k;\n"
      "wire [2:0] a; wire [3:0] b, c;\n"
      "assign a = n[P:2]; assign b = n[2+:P]; assign c = n[k+:P];\n"
      "endmodule\n");
  const std::vector<vpiHandle> kSides = RightSides(By("top"));
  ASSERT_EQ(kSides.size(), 3U);
  EXPECT_EQ(vpi_get(vpiType, kSides[0]), vpiPartSelect);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kSides[0]), 1);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kSides[1]), 1);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kSides[2]), 0);
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

// §37.58 detail 3: a bit select whose index is a variable is no constant
// select...
TEST_F(BitSelectsOfARun, ABitSelectByAVariableIsNoConstantSelect) {
  Run("module top; integer i, j; wire w; assign w = i[j]; endmodule\n");
  EXPECT_EQ(vpi_get(vpiConstantSelect, Rhs()), 0);
}

// ...where one by a constant of a static variable is.
TEST_F(BitSelectsOfARun, ABitSelectByAConstantIsAConstantSelect) {
  Run(kIntegerBit);
  EXPECT_EQ(vpi_get(vpiConstantSelect, Rhs()), 1);
}

// §37.58: a bit select is named by its parent and the index it was written
// with...
TEST_F(BitSelectsOfARun, ABitSelectIsNamedByItsParentAndIndex) {
  Run(kIntegerBit);
  EXPECT_STREQ(vpi_get_str(vpiName, Rhs()), "i[3]");
}

// ...under the parent's full name.
TEST_F(BitSelectsOfARun, ABitSelectsFullNameIsItsParents) {
  Run(kIntegerBit);
  EXPECT_STREQ(vpi_get_str(vpiFullName, Rhs()), "top.i[3]");
}

constexpr const char* kElementBit =
    "module top; logic [7:0] arr [0:3]; wire y; assign y = arr[1][3];\n"
    "endmodule\n";

// §37.17 details 2 and 18: an element of an array of vectors is a variable of
// the element's type, so a bit of it is one of its var bits...
TEST_F(BitSelectsOfARun, ABitOfAnElementIsTheElementsVarBit) {
  Run(kElementBit);
  vpiHandle element = vpi_handle_by_index(By("top.arr"), 1);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(vpi_get(vpiType, Rhs()), vpiRegBit);
  EXPECT_EQ(Rhs(), vpi_handle_by_index(element, 3));
}

// ...none of which is an index of the element.
TEST_F(BitSelectsOfARun, AnElementsBitsAreNoIndicesOfIt) {
  Run(kElementBit);
  vpiHandle element = vpi_handle_by_index(By("top.arr"), 1);
  ASSERT_NE(element, nullptr);
  vpiHandle it = vpi_iterate(vpiIndex, element);
  ASSERT_NE(it, nullptr);
  int count = 0;
  while (vpi_scan(it) != nullptr) ++count;
  EXPECT_EQ(count, 1);
}

// The integer property `property` of each object vpiUse reaches from `expr`,
// lowest first.
std::vector<int> PropertyOfUses(int property, vpiHandle expr) {
  std::vector<int> values;
  vpiHandle it = vpi_iterate(vpiUse, expr);
  if (it == nullptr) return values;
  for (vpiHandle use = vpi_scan(it); use != nullptr; use = vpi_scan(it)) {
    values.push_back(vpi_get(property, use));
  }
  std::ranges::sort(values);
  return values;
}

// The lines the objects vpiUse reaches from `expr` were written on, lowest
// first.
std::vector<int> LinesOfUses(vpiHandle expr) {
  return PropertyOfUses(vpiLineNo, expr);
}

// The kinds of the objects vpiUse reaches from `expr`, lowest first.
std::vector<int> KindsOfUses(vpiHandle expr) {
  return PropertyOfUses(vpiType, expr);
}

// `kinds`, lowest first, to set against KindsOfUses.
std::vector<int> Ascending(std::vector<int> kinds) {
  std::ranges::sort(kinds);
  return kinds;
}

// §37.58 detail 1: the uses of a vector are those of the vector and of its
// bit and part selects, a continuous assignment and a statement among them,
// and no other.
TEST_F(BitSelectsOfARun, AVectorIsUsedWhereItOrASelectOfItIs) {
  Run("module top; logic [7:0] v; wire a, b, c; logic [7:0] w;\n"
      "assign a = v[2];\n"
      "assign b = c;\n"
      "assign c = |v[5:4];\n"
      "initial w = v;\n"
      "endmodule\n");
  EXPECT_EQ(LinesOfUses(By("top.v")), (std::vector<int>{2, 4, 5}));
}

// §37.58 detail 2: the uses of a bit select are those of that bit, of the
// vector it selects from and of a part select of the vector holding it, and
// not one of another bit.
TEST_F(BitSelectsOfARun, ABitIsUsedWhereItItsVectorOrASelectHoldingItIs) {
  Run("module top; integer i, j; wire a, b, c, d;\n"
      "assign a = i[3];\n"
      "assign b = i[3];\n"
      "assign c = i[5];\n"
      "assign d = ^i[4:2];\n"
      "initial j = i;\n"
      "endmodule\n");
  EXPECT_EQ(LinesOfUses(Rhs()), (std::vector<int>{2, 3, 5, 6}));
}

// §37.58 detail 1: a vector is used through a select of any kind written of
// it -- a bit select of an integer var, an indexed part select, a net bit, a
// varying var bit and a var select of an array -- and a variable is used
// where it indexes such a select.
TEST_F(BitSelectsOfARun, AVectorIsUsedThroughEverySelectKindAndAnIndex) {
  Run("module top; integer i; logic [7:0] v; wire [3:0] n;\n"
      "logic [7:0] arr [0:3]; wire a, b, c, y;\n"
      "assign a = i[3];\n"
      "assign b = ^v[2+:2];\n"
      "assign c = n[1] | v[i];\n"
      "assign y = ^arr[i];\n"
      "endmodule\n");
  EXPECT_EQ(LinesOfUses(By("top.i")), (std::vector<int>{3, 5, 6}));
  EXPECT_EQ(LinesOfUses(By("top.v")), (std::vector<int>{4, 5}));
  EXPECT_EQ(LinesOfUses(By("top.n")), (std::vector<int>{5}));
  EXPECT_EQ(LinesOfUses(By("top.arr")), (std::vector<int>{6}));
}

// §37.58 detail 2 for a bit of a net: a part select or an indexed part
// select, up or down, of the net is a use where its constant bounds hold the
// bit, and not where they lie below or above it.
TEST_F(BitSelectsOfARun, ANetBitIsUsedWhereASelectsBoundsHoldIt) {
  Run("module top; wire [7:0] n; wire a, b, c, d, e, f;\n"
      "assign a = n[3];\n"
      "assign b = ^n[5:2];\n"
      "assign c = ^n[2+:2];\n"
      "assign d = ^n[4-:2];\n"
      "assign e = ^n[2:0];\n"
      "assign f = ^n[6:4];\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, Rhs()), vpiNetBit);
  EXPECT_EQ(LinesOfUses(Rhs()), (std::vector<int>{2, 3, 4, 5}));
}

// §37.58 detail 2 with §11.5.1: the bounds, base and width of a part select
// are constant expressions, a parameter among them, so one bounded by a
// parameter, based on one, or of a parameter width holds the bits their values
// span, and uses a bit it holds. A bit selected by a variable is no specific
// use of the bit, whichever bit the variable picks out.
TEST_F(BitSelectsOfARun, ANetBitIsUsedWhereAParameterBoundedSelectHoldsIt) {
  Run("module top; parameter P = 4; wire [7:0] n; integer k;\n"
      "wire a, b, c, d, e; assign a = n[3];\n"
      "assign b = ^n[P:2];\n"
      "assign c = ^n[2+:P];\n"
      "assign d = ^n[P+:2];\n"
      "assign e = n[k];\n"
      "endmodule\n");
  EXPECT_EQ(LinesOfUses(Rhs()), (std::vector<int>{2, 3, 4}));
}

// The same of a genvar, which stands for a constant in each block its loop
// generates (§27.4): of the two blocks below, the select of the first, based
// at 2, holds the bit, and that of the second, based at 4, does not.
TEST_F(BitSelectsOfARun, ANetBitIsUsedWhereAGenvarBasedSelectHoldsIt) {
  Run("module top; wire [7:0] n; wire a;\n"
      "assign a = n[3];\n"
      "for (genvar g = 2; g < 5; g += 2) begin : blk\n"
      "  wire b;\n"
      "  assign b = ^n[g+:2];\n"
      "end\n"
      "endmodule\n");
  EXPECT_EQ(LinesOfUses(Rhs()), (std::vector<int>{2, 5}));
}

// §37.58 detail 2 on objects the model holds no index or bounds for: a bit
// matches another bit of its vector, or a part select of it, by the values of
// their indices and bounds alone, a constant's, a parameter's or a spec
// param's. A bit with no index, a bit whose index holds no value, and a part
// select missing a bound, its base or its width match none, while a bit at
// the same index does.
TEST(SimpleExpressionModel, ABitMatchesASelectOnlyByConstantValues) {
  Arena arena;
  Variable three_value;
  three_value.value = MakeLogic4VecVal(arena, 32, 3);
  VpiObject three;
  three.type = vpiConstant;
  three.var = &three_value;
  VpiObject valueless;
  valueless.type = vpiConstant;
  VpiObject vector;
  vector.type = vpiLogicVar;
  const auto kSelectOf = [&vector](int type) {
    VpiObject select;
    select.type = type;
    select.parent = &vector;
    return select;
  };

  VpiObject bit = kSelectOf(vpiRegBit);
  bit.index_expr = &three;
  VpiObject twin = kSelectOf(vpiRegBit);
  twin.index_expr = &three;
  EXPECT_TRUE(VpiExpressionUses(&twin, bit));
  VpiObject spec_three;
  spec_three.type = vpiSpecParam;
  spec_three.var = &three_value;
  VpiObject spec_twin = kSelectOf(vpiRegBit);
  spec_twin.index_expr = &spec_three;
  EXPECT_TRUE(VpiExpressionUses(&spec_twin, bit));
  VpiObject no_value = kSelectOf(vpiRegBit);
  no_value.index_expr = &valueless;
  EXPECT_FALSE(VpiExpressionUses(&no_value, bit));
  VpiObject no_index = kSelectOf(vpiRegBit);
  EXPECT_FALSE(VpiExpressionUses(&bit, no_index));

  VpiObject no_left = kSelectOf(vpiPartSelect);
  no_left.right_range = &three;
  EXPECT_FALSE(VpiExpressionUses(&no_left, bit));
  VpiObject no_right = kSelectOf(vpiPartSelect);
  no_right.left_range = &three;
  EXPECT_FALSE(VpiExpressionUses(&no_right, bit));
  VpiObject no_base = kSelectOf(vpiIndexedPartSelect);
  no_base.width_expr = &three;
  EXPECT_FALSE(VpiExpressionUses(&no_base, bit));
  VpiObject no_width = kSelectOf(vpiIndexedPartSelect);
  no_width.base_expr = &three;
  EXPECT_FALSE(VpiExpressionUses(&no_width, bit));
}

// A cell whose input `a` feeds a gate, a module path and a timing check, and
// whose output `y` the gate drives and the path's delay device stands on
// (§37.45), instanced in a top driving a two-bit wire by a continuous
// assignment of its own.
constexpr const char* kTimedCell =
    "module m(input a, input c, output y);\n"
    "  buf g(y, a);\n"
    "  specify (a => y) = 3; $setup(a, posedge c, 1); endspecify\n"
    "endmodule\n"
    "module top; wire p, q, r; wire [1:0] w; assign w = 2'b01;\n"
    "  m u(p, r, q);\n"
    "endmodule\n";

// §37.58 (figure): of the prim terms, path terms, tchk terms, ports and
// continuous assignments and their bits a design holds, a wire is used by the
// ones naming it. The cell's gate, module path and timing check and the top's
// vector assignment name other signals, so the port the wire connects is its
// one use.
TEST_F(BitSelectsOfARun, AWireIsUsedByThePortItConnectsAlone) {
  Run(kTimedCell);
  vpiHandle it = vpi_iterate(vpiUse, By("top.p"));
  ASSERT_NE(it, nullptr);
  vpiHandle use = vpi_scan(it);
  ASSERT_NE(use, nullptr);
  EXPECT_EQ(vpi_get(vpiType, use), vpiPort);
  EXPECT_STREQ(vpi_get_str(vpiName, use), "a");
  EXPECT_EQ(vpi_scan(it), nullptr);
}

// §37.58 (figure) with §37.39 and §37.40: a path term and a tchk term whose
// terminal names a net use it, so the cell's input is used by the input term
// of its module path and the data term of its timing check, beside its gate's
// prim term and its port.
TEST_F(BitSelectsOfARun, ACellInputIsUsedByItsPathAndTimingCheckTerms) {
  Run(kTimedCell);
  EXPECT_EQ(KindsOfUses(By("top.u.a")),
            Ascending({vpiPort, vpiPrimTerm, vpiPathTerm, vpiTchkTerm}));
}

// §37.58 (figure) with §37.45: the two delay terms of a delay device stand on
// the net it is placed on and use it, so the cell's output is used by those of
// its module path's device, beside its gate's prim term, the path's output term
// and its port.
TEST_F(BitSelectsOfARun, ACellOutputIsUsedByItsPathDevicesDelayTerms) {
  Run(kTimedCell);
  EXPECT_EQ(KindsOfUses(By("top.u.y")),
            Ascending({vpiPort, vpiPrimTerm, vpiPathTerm, vpiDelayTerm,
                       vpiDelayTerm}));
}

// §37.58 (figure) with §37.47: a cont assign bit has no sides of its own, its
// value being its bit of its assignment's, so it uses what the assignment
// uses: a vector read by a two-bit assignment is used by the assignment and by
// both its bits.
TEST_F(BitSelectsOfARun, AnAssignmentsBitsUseWhatTheAssignmentUses) {
  Run("module top; logic [1:0] v; wire [1:0] w; assign w = v; endmodule\n");
  EXPECT_EQ(KindsOfUses(By("top.v")),
            Ascending({vpiContAssign, vpiContAssignBit, vpiContAssignBit}));
}

// ...and a cont assign bit belonging to no assignment uses nothing.
TEST(SimpleExpressionModel, AnAssignmentBitOfNoAssignmentUsesNothing) {
  VpiObject net;
  net.type = vpiNet;
  VpiObject bit;
  bit.type = vpiContAssignBit;
  EXPECT_FALSE(VpiUsesExpr(bit, net));
}

// §37.58 (figure): the simple expressions are the nets, the variables, a ref
// obj, a parameter, a spec param, a var select and a bit select; no other
// object, and no object at all, is one.
TEST(SimpleExpressionModel, TheSimpleExpressionsAreTheFiguresKinds) {
  EXPECT_FALSE(VpiIsSimpleExpr(nullptr));
  for (int type :
       {vpiRefObj, vpiParameter, vpiSpecParam, vpiVarSelect, vpiBitSelect,
        vpiNet, vpiNetBit, vpiLogicVar, vpiIntegerVar}) {
    VpiObject obj;
    obj.type = type;
    EXPECT_TRUE(VpiIsSimpleExpr(&obj)) << type;
  }
  for (int type : {vpiPartSelect, vpiOperation, vpiConstant, vpiModule}) {
    VpiObject obj;
    obj.type = type;
    EXPECT_FALSE(VpiIsSimpleExpr(&obj)) << type;
  }
}

// §37.58 details 1 and 2 on objects standing in no design: a select reaching
// no object through vpiParent selects out of no vector and uses none, and a
// bit with no parent is used only where that very bit stands.
TEST(SimpleExpressionModel, ASelectOrBitOfNothingIsUsedOnlyWhereItStands) {
  VpiObject vector;
  vector.type = vpiLogicVar;
  VpiObject select;
  select.type = vpiPartSelect;
  EXPECT_FALSE(VpiExpressionUses(&select, vector));

  VpiObject bit;
  bit.type = vpiBitSelect;
  VpiObject other;
  other.type = vpiBitSelect;
  EXPECT_FALSE(VpiExpressionUses(&other, bit));
  EXPECT_TRUE(VpiExpressionUses(&bit, bit));
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
// §11.2.1 read off the objects: a constant, a parameter and a spec param are
// elaboration-time constants, and an operation is one where each of its
// operands is, the attributes its operator carries being none of them. No
// object, a variable and an operation over one are none.
TEST(SimpleExpressionModel, ElaborationConstantsAreConstantsAndParameters) {
  EXPECT_FALSE(VpiIsElaborationConstant(nullptr));
  VpiObject spec;
  spec.type = vpiSpecParam;
  EXPECT_TRUE(VpiIsElaborationConstant(&spec));
  VpiObject attribute;
  attribute.type = vpiAttribute;
  VpiObject operation;
  operation.type = vpiOperation;
  operation.children = {&spec, &attribute};
  EXPECT_TRUE(VpiIsElaborationConstant(&operation));
  VpiObject var;
  var.type = vpiIntegerVar;
  EXPECT_FALSE(VpiIsElaborationConstant(&var));
  operation.children.push_back(&var);
  EXPECT_FALSE(VpiIsElaborationConstant(&operation));
}

// A design run with a PLI application registered, its VPI model read back
// once the run is over.
class ConstantsOfARun : public VpiDesignRun {};

// §37.58 with §5.8: a time literal is a constant of type vpiTimeConst holding
// its value in the module's time unit (#5758).
TEST_F(ConstantsOfARun, ATimeLiteralIsATimeConstant) {
  Run("module top; timeunit 1ns; timeprecision 1ps;\n"
      "  realtime r; assign r = 2.5ns; endmodule\n");
  vpiHandle it = vpi_iterate(vpiContAssign, By("top"));
  ASSERT_NE(it, nullptr);
  vpiHandle literal = vpi_handle(vpiRhs, vpi_scan(it));
  ASSERT_NE(literal, nullptr);
  EXPECT_EQ(vpi_get(vpiType, literal), vpiConstant);
  EXPECT_EQ(vpi_get(vpiConstType, literal), vpiTimeConst);
  s_vpi_value value = {};
  value.format = vpiRealVal;
  vpi_get_value(literal, &value);
  EXPECT_DOUBLE_EQ(value.value.real, 2.5);
}

}  // namespace
}  // namespace delta
