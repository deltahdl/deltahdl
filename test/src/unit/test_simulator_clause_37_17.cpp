#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.17 Variables: the VPI variable object model. These tests observe the
// production helpers in vpi.cpp that apply the numbered "Details" of the clause.
// The range relations (details 4 and 6) are woven onto §37.22's range helpers,
// so an empty dimension behaves the same here as it does there. Lifetime and
// memory-allocation properties (detail 23) belong to §37.3.7, and struct/union
// member access (detail 3) to §37.26, so those are exercised by their own
// subclauses.

// D19: the backward-compatibility object-kind equivalences. A var bit is the
// same kind as a reg bit; a logic var is equivalent to a reg, and an array var
// to a reg array.
TEST(VariableModel, BackwardCompatibilityKindEquivalences) {
  EXPECT_EQ(vpiVarBit, vpiRegBit);
  EXPECT_TRUE(VpiIsLogicVarType(vpiLogicVar));
  EXPECT_TRUE(VpiIsLogicVarType(vpiReg));
  EXPECT_TRUE(VpiIsArrayVarType(vpiArrayVar));
  EXPECT_TRUE(VpiIsArrayVarType(vpiRegArray));
  EXPECT_FALSE(VpiIsLogicVarType(vpiBitVar));
  EXPECT_FALSE(VpiIsArrayVarType(vpiStructVar));
}

// D1: a variable declared as an array with one or more unpacked ranges is an
// array var; with no unpacked ranges it is not.
TEST(VariableModel, ArrayVarRequiresAtLeastOneUnpackedRange) {
  EXPECT_TRUE(VpiIsArrayVar(1));
  EXPECT_TRUE(VpiIsArrayVar(3));
  EXPECT_FALSE(VpiIsArrayVar(0));
}

// D2: vpiArrayMember is TRUE when the variable's vpiParent prefix is an array
// variable (a reg array counts, per detail 19), FALSE otherwise.
TEST(VariableModel, ArrayMemberReadsArrayVarParent) {
  VpiObject array_var;
  array_var.type = vpiArrayVar;
  VpiObject element;
  element.type = vpiLogicVar;
  element.parent = &array_var;
  EXPECT_TRUE(VpiVariableIsArrayMember(&element));

  VpiObject reg_array;
  reg_array.type = vpiRegArray;
  element.parent = &reg_array;
  EXPECT_TRUE(VpiVariableIsArrayMember(&element));

  VpiObject struct_var;
  struct_var.type = vpiStructVar;
  element.parent = &struct_var;
  EXPECT_FALSE(VpiVariableIsArrayMember(&element));

  element.parent = nullptr;
  EXPECT_FALSE(VpiVariableIsArrayMember(&element));
  EXPECT_FALSE(VpiVariableIsArrayMember(nullptr));
}

// D17: vpiStructUnionMember is TRUE when the vpiParent prefix is a struct or
// union variable.
TEST(VariableModel, StructUnionMemberReadsStructOrUnionParent) {
  VpiObject struct_var;
  struct_var.type = vpiStructVar;
  VpiObject member;
  member.type = vpiIntVar;
  member.parent = &struct_var;
  EXPECT_TRUE(VpiVariableIsStructUnionMember(&member));

  VpiObject union_var;
  union_var.type = vpiUnionVar;
  member.parent = &union_var;
  EXPECT_TRUE(VpiVariableIsStructUnionMember(&member));

  VpiObject array_var;
  array_var.type = vpiArrayVar;
  member.parent = &array_var;
  EXPECT_FALSE(VpiVariableIsStructUnionMember(&member));
  EXPECT_FALSE(VpiVariableIsStructUnionMember(nullptr));
}

// D4 (woven with §37.22): the vpiRange iteration returns one range per dimension
// from leftmost to rightmost. A fixed dimension keeps its bounds; a dynamic,
// queue, or associative dimension becomes an empty range with null bounds.
TEST(VariableModel, RangeIterationYieldsBoundsOrEmptyPerDimension) {
  VpiObject l0;
  VpiObject r0;
  std::vector<VpiArrayDimension> dims(4);
  dims[0].kind = VpiDimensionKind::kFixedUnpacked;
  dims[0].left_expr = &l0;
  dims[0].right_expr = &r0;
  dims[0].size = 4;
  dims[1].kind = VpiDimensionKind::kDynamic;
  dims[2].kind = VpiDimensionKind::kAssoc;
  dims[3].kind = VpiDimensionKind::kQueue;

  std::vector<VpiRangeDesc> ranges = VpiArrayVarRanges(dims);
  ASSERT_EQ(ranges.size(), 4u);

  // Leftmost fixed dimension keeps its bounds and size.
  EXPECT_EQ(VpiRangeLeftRange(ranges[0]), &l0);
  EXPECT_EQ(VpiRangeRightRange(ranges[0]), &r0);
  EXPECT_EQ(VpiRangeSize(ranges[0]), 4);

  // Dynamic, associative, and queue dimensions are all empty ranges (§37.22).
  EXPECT_EQ(VpiRangeLeftRange(ranges[1]), nullptr);
  EXPECT_EQ(VpiRangeSize(ranges[1]), 0);
  EXPECT_EQ(VpiRangeRightRange(ranges[2]), nullptr);
  EXPECT_EQ(VpiRangeSize(ranges[2]), 0);
  EXPECT_EQ(VpiRangeLeftRange(ranges[3]), nullptr);
  EXPECT_EQ(VpiRangeSize(ranges[3]), 0);
}

// D4: the ranges returned for a packed array exclude the implicit range of a
// packed struct/union element and an enum var's base type.
TEST(VariableModel, RangeIterationDropsImplicitElementRanges) {
  VpiObject l;
  VpiObject r;
  std::vector<VpiArrayDimension> dims(2);
  dims[0].kind = VpiDimensionKind::kPacked;
  dims[0].left_expr = &l;
  dims[0].right_expr = &r;
  dims[0].size = 8;
  dims[1].kind = VpiDimensionKind::kPacked;
  dims[1].implicit_element_range = true;  // element's own implicit range

  std::vector<VpiRangeDesc> ranges = VpiArrayVarRanges(dims);
  ASSERT_EQ(ranges.size(), 1u);
  EXPECT_EQ(VpiRangeLeftRange(ranges[0]), &l);
}

// D6 (woven with §37.22): vpiLeftRange/vpiRightRange report the leftmost
// dimension's bounds.
TEST(VariableModel, LeftRightRangeReportLeftmostDimensionBounds) {
  VpiObject l;
  VpiObject r;
  std::vector<VpiArrayDimension> dims(2);
  dims[0].kind = VpiDimensionKind::kPacked;
  dims[0].left_expr = &l;
  dims[0].right_expr = &r;
  dims[1].kind = VpiDimensionKind::kPacked;  // a later dimension is ignored here

  EXPECT_EQ(VpiVariableLeftRange(dims, /*has_members=*/true), &l);
  EXPECT_EQ(VpiVariableRightRange(dims, /*has_members=*/true), &r);
}

// D6: vpiLeftRange/vpiRightRange return NULL when the variable has no members or
// when the leftmost range is empty.
TEST(VariableModel, LeftRightRangeNullForNoMembersOrEmptyRange) {
  VpiObject l;
  VpiObject r;
  std::vector<VpiArrayDimension> dims(1);
  dims[0].kind = VpiDimensionKind::kFixedUnpacked;
  dims[0].left_expr = &l;
  dims[0].right_expr = &r;

  // No members -> NULL even though a fixed range is present.
  EXPECT_EQ(VpiVariableLeftRange(dims, /*has_members=*/false), nullptr);
  EXPECT_EQ(VpiVariableRightRange(dims, /*has_members=*/false), nullptr);

  // An empty leftmost dimension -> NULL (§37.22).
  std::vector<VpiArrayDimension> assoc(1);
  assoc[0].kind = VpiDimensionKind::kAssoc;
  EXPECT_EQ(VpiVariableLeftRange(assoc, /*has_members=*/true), nullptr);
  EXPECT_EQ(VpiVariableRightRange(assoc, /*has_members=*/true), nullptr);

  // No dimensions at all -> NULL.
  EXPECT_EQ(VpiVariableLeftRange({}, /*has_members=*/true), nullptr);
}

// D8: a variable's initialization expression is reached through vpiExpr; a
// variable with no initialization expression has none.
TEST(VariableModel, InitializationExpressionReachedThroughExpr) {
  VpiObject init;
  VpiObject var;
  var.children.push_back(&init);
  EXPECT_EQ(VpiVariableInitExpr(&var), &init);

  VpiObject uninitialized;
  EXPECT_EQ(VpiVariableInitExpr(&uninitialized), nullptr);
  EXPECT_EQ(VpiVariableInitExpr(nullptr), nullptr);
}

// D5: vpi_handle(vpiIndex, var_select) returns the single innermost index of a
// one-dimensional var select.
TEST(VariableModel, VarSelectSingleIndexIsTheInnermost) {
  VpiObject i0;
  VpiObject i1;
  std::vector<VpiHandle> indices = {&i0, &i1};
  EXPECT_EQ(VpiSelectSingleIndex(indices), &i0);
  EXPECT_EQ(VpiSelectSingleIndex({}), nullptr);
}

// D5/D13/D18: the vpiIndex iteration runs from the innermost index outward,
// shared by var selects, var bits, and array-member variables.
TEST(VariableModel, IndexIterationRunsInnermostOutward) {
  VpiObject inner;
  VpiObject middle;
  VpiObject outer;
  std::vector<VpiHandle> indices = {&inner, &middle, &outer};
  std::vector<VpiHandle> out = VpiSelectIndicesOutward(indices);
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0], &inner);
  EXPECT_EQ(out[2], &outer);
}

// D9: vpiSize for the kinds whose size is defined - a variable array reports its
// element count; integer-typed, packed, and enum vars report bit width; a string
// var reports its character count; an unpacked struct/union reports field count;
// a var bit reports 1.
TEST(VariableModel, SizeFollowsTheVariableKind) {
  VpiVariableSizeQuery q;

  q = {};
  q.var_type = vpiArrayVar;
  q.array_element_count = 6;
  EXPECT_EQ(VpiVariableSize(q), 6);

  q = {};
  q.var_type = vpiIntVar;
  q.bit_width = 32;
  EXPECT_EQ(VpiVariableSize(q), 32);

  q = {};
  q.var_type = vpiLogicVar;  // reg-equivalent
  q.bit_width = 8;
  EXPECT_EQ(VpiVariableSize(q), 8);

  q = {};
  q.var_type = vpiEnumVar;
  q.bit_width = 3;
  EXPECT_EQ(VpiVariableSize(q), 3);

  q = {};
  q.var_type = vpiStringVar;
  q.string_length = 5;
  EXPECT_EQ(VpiVariableSize(q), 5);

  q = {};
  q.var_type = vpiStructVar;  // unpacked struct -> field count
  q.packed = false;
  q.field_count = 4;
  EXPECT_EQ(VpiVariableSize(q), 4);

  q = {};
  q.var_type = vpiStructVar;  // packed struct -> bits
  q.packed = true;
  q.bit_width = 17;
  EXPECT_EQ(VpiVariableSize(q), 17);

  q = {};
  q.var_type = vpiUnionVar;  // unpacked union -> field count
  q.packed = false;
  q.field_count = 2;
  EXPECT_EQ(VpiVariableSize(q), 2);

  q = {};
  q.var_type = vpiUnionVar;  // packed union -> bits
  q.packed = true;
  q.bit_width = 9;
  EXPECT_EQ(VpiVariableSize(q), 9);

  q = {};
  q.var_type = vpiVarBit;
  EXPECT_EQ(VpiVariableSize(q), 1);
}

// D9: every integer data-type kind, and a packed array var, report their bit
// width through vpiSize (each is a distinct variable kind in the production
// switch).
TEST(VariableModel, SizeForIntegerTypedAndPackedArrayKinds) {
  for (int kind : {vpiByteVar, vpiShortIntVar, vpiLongIntVar, vpiIntegerVar,
                   vpiTimeVar, vpiBitVar, vpiPackedArrayVar}) {
    VpiVariableSizeQuery q;
    q.var_type = kind;
    q.bit_width = 16;
    EXPECT_EQ(VpiVariableSize(q), 16) << "kind=" << kind;
  }
}

// D10: vpiSize for a packed var select is its number of bits.
TEST(VariableModel, VarSelectSizeIsBitCount) {
  VpiVariableSizeQuery q;
  q.var_type = vpiVarSelect;
  q.bit_width = 12;
  EXPECT_EQ(VpiVariableSize(q), 12);
}

// D9: for variable kinds whose vpiSize is not defined, the helper reports 0.
TEST(VariableModel, SizeIsZeroWhenUndefined) {
  VpiVariableSizeQuery q;
  q.var_type = vpiChandleVar;
  EXPECT_EQ(VpiVariableSize(q), 0);
}

// D11: array, class, and virtual-interface variables have no value property, and
// neither does an unpacked struct/union; every other kind does.
TEST(VariableModel, ValuePropertyAvailability) {
  EXPECT_FALSE(VpiVariableHasValueProperty(vpiArrayVar, /*vpi_vector=*/false));
  EXPECT_FALSE(VpiVariableHasValueProperty(vpiClassVar, false));
  EXPECT_FALSE(
      VpiVariableHasValueProperty(vpiVirtualInterfaceVar, false));
  // Unpacked struct/union (vpiVector FALSE) has none; packed (TRUE) has one.
  EXPECT_FALSE(VpiVariableHasValueProperty(vpiStructVar, /*vpi_vector=*/false));
  EXPECT_TRUE(VpiVariableHasValueProperty(vpiStructVar, /*vpi_vector=*/true));
  EXPECT_FALSE(VpiVariableHasValueProperty(vpiUnionVar, /*vpi_vector=*/false));
  EXPECT_TRUE(VpiVariableHasValueProperty(vpiUnionVar, /*vpi_vector=*/true));
  EXPECT_TRUE(VpiVariableHasValueProperty(vpiLogicVar, false));
  EXPECT_TRUE(VpiVariableHasValueProperty(vpiIntVar, false));
}

// D12: the vpiBit iterator applies only to logic, bit, packed struct, packed
// union, and packed array variables.
TEST(VariableModel, BitIteratorApplicability) {
  EXPECT_TRUE(VpiBitIteratorApplies(vpiLogicVar, /*packed=*/false));
  EXPECT_TRUE(VpiBitIteratorApplies(vpiBitVar, false));
  EXPECT_TRUE(VpiBitIteratorApplies(vpiPackedArrayVar, false));
  EXPECT_TRUE(VpiBitIteratorApplies(vpiStructVar, /*packed=*/true));
  EXPECT_FALSE(VpiBitIteratorApplies(vpiStructVar, /*packed=*/false));
  EXPECT_TRUE(VpiBitIteratorApplies(vpiUnionVar, /*packed=*/true));
  EXPECT_FALSE(VpiBitIteratorApplies(vpiUnionVar, /*packed=*/false));
  EXPECT_FALSE(VpiBitIteratorApplies(vpiIntVar, false));
  EXPECT_FALSE(VpiBitIteratorApplies(vpiStringVar, false));
}

// D15/D22: vpiRandType is one of vpiRand, vpiRandC, vpiNotRand.
TEST(VariableModel, RandTypeDomain) {
  EXPECT_TRUE(VpiIsRandTypeValue(vpiRand));
  EXPECT_TRUE(VpiIsRandTypeValue(vpiRandC));
  EXPECT_TRUE(VpiIsRandTypeValue(vpiNotRand));
  EXPECT_FALSE(VpiIsRandTypeValue(0));
  EXPECT_FALSE(VpiIsRandTypeValue(99));
}

// D16: vpiIsRandomized reports whether a random variable is currently active.
TEST(VariableModel, IsRandomizedReflectsActiveness) {
  EXPECT_TRUE(VpiIsRandomized(true));
  EXPECT_FALSE(VpiIsRandomized(false));
}

// D14: cbSizeChange applies only to dynamic arrays, associative arrays, queues,
// and string variables - not to static arrays or any other variable.
TEST(VariableModel, SizeChangeCallbackApplicability) {
  EXPECT_TRUE(VpiSizeChangeCallbackApplies(vpiDynamicArray, /*is_string=*/false));
  EXPECT_TRUE(VpiSizeChangeCallbackApplies(vpiAssocArray, false));
  EXPECT_TRUE(VpiSizeChangeCallbackApplies(vpiQueueArray, false));
  EXPECT_TRUE(VpiSizeChangeCallbackApplies(/*array_type=*/0, /*is_string=*/true));
  EXPECT_FALSE(VpiSizeChangeCallbackApplies(vpiStaticArray, false));
  EXPECT_FALSE(VpiSizeChangeCallbackApplies(/*array_type=*/0, false));
}

// D21: vpiArrayType is one of the four array-type values.
TEST(VariableModel, ArrayTypeDomain) {
  EXPECT_TRUE(VpiIsArrayTypeValue(vpiStaticArray));
  EXPECT_TRUE(VpiIsArrayTypeValue(vpiDynamicArray));
  EXPECT_TRUE(VpiIsArrayTypeValue(vpiAssocArray));
  EXPECT_TRUE(VpiIsArrayTypeValue(vpiQueueArray));
  EXPECT_FALSE(VpiIsArrayTypeValue(0));
}

// D20: scalar/vector for a bit/logic var depends on whether a packed dimension
// is present.
TEST(VariableModel, ScalarVectorForBitAndLogicVar) {
  VpiScalarVectorQuery q;
  q.var_type = vpiLogicVar;
  q.has_packed_dimension = false;
  EXPECT_TRUE(VpiVariableScalar(q));
  EXPECT_FALSE(VpiVariableVector(q));

  q.has_packed_dimension = true;
  EXPECT_FALSE(VpiVariableScalar(q));
  EXPECT_TRUE(VpiVariableVector(q));

  q.var_type = vpiBitVar;
  q.has_packed_dimension = false;
  EXPECT_TRUE(VpiVariableScalar(q));
  EXPECT_FALSE(VpiVariableVector(q));
}

// D20: a var bit is a scalar; packed struct/union/array and the integer-typed
// vars are vectors; an unpacked struct/union and a string var are neither.
TEST(VariableModel, ScalarVectorForOtherKinds) {
  VpiScalarVectorQuery q;

  q = {};
  q.var_type = vpiVarBit;
  EXPECT_TRUE(VpiVariableScalar(q));
  EXPECT_FALSE(VpiVariableVector(q));

  q = {};
  q.var_type = vpiPackedArrayVar;
  EXPECT_FALSE(VpiVariableScalar(q));
  EXPECT_TRUE(VpiVariableVector(q));

  q = {};
  q.var_type = vpiStructVar;
  q.packed = true;
  EXPECT_TRUE(VpiVariableVector(q));
  q.packed = false;
  EXPECT_FALSE(VpiVariableVector(q));
  EXPECT_FALSE(VpiVariableScalar(q));

  q = {};
  q.var_type = vpiUnionVar;  // a packed union is a vector, unpacked is neither
  q.packed = true;
  EXPECT_TRUE(VpiVariableVector(q));
  q.packed = false;
  EXPECT_FALSE(VpiVariableVector(q));
  EXPECT_FALSE(VpiVariableScalar(q));

  q = {};
  q.var_type = vpiStringVar;  // an "all other" object - neither
  EXPECT_FALSE(VpiVariableScalar(q));
  EXPECT_FALSE(VpiVariableVector(q));
}

// D20: every integer data-type kind is a vector and not a scalar (each is a
// distinct kind in the production switch).
TEST(VariableModel, VectorForAllIntegerTypedKinds) {
  for (int kind : {vpiIntegerVar, vpiTimeVar, vpiShortIntVar, vpiIntVar,
                   vpiLongIntVar, vpiByteVar}) {
    VpiScalarVectorQuery q;
    q.var_type = kind;
    EXPECT_TRUE(VpiVariableVector(q)) << "kind=" << kind;
    EXPECT_FALSE(VpiVariableScalar(q)) << "kind=" << kind;
  }
}

// D20: an enum var defers to its base typespec, and an array var to an element.
TEST(VariableModel, ScalarVectorDeferForEnumAndArray) {
  VpiScalarVectorQuery enum_q;
  enum_q.var_type = vpiEnumVar;
  enum_q.base_is_scalar = true;
  enum_q.base_is_vector = false;
  EXPECT_TRUE(VpiVariableScalar(enum_q));
  EXPECT_FALSE(VpiVariableVector(enum_q));

  VpiScalarVectorQuery array_q;
  array_q.var_type = vpiArrayVar;
  array_q.element_is_scalar = false;
  array_q.element_is_vector = true;
  EXPECT_FALSE(VpiVariableScalar(array_q));
  EXPECT_TRUE(VpiVariableVector(array_q));
}

// D24: a non-class-member variable, and a class member that is neither local nor
// protected, report vpiPublicVis; local/protected members report their own
// visibility.
TEST(VariableModel, VisibilityRules) {
  EXPECT_EQ(VpiVariableVisibility(/*is_class_member=*/false, vpiLocalVis),
            vpiPublicVis);
  EXPECT_EQ(VpiVariableVisibility(/*is_class_member=*/true, vpiPublicVis),
            vpiPublicVis);
  EXPECT_EQ(VpiVariableVisibility(/*is_class_member=*/true, vpiLocalVis),
            vpiLocalVis);
  EXPECT_EQ(VpiVariableVisibility(/*is_class_member=*/true, vpiProtectedVis),
            vpiProtectedVis);
}

// D25: a non-static class data member has no vpiFullName; a static member's full
// name routes through its class defn with "::".
TEST(VariableModel, ClassMemberFullName) {
  EXPECT_EQ(VpiClassMemberFullName(/*is_static=*/false, "top", "Packet", "Id"),
            "");
  EXPECT_EQ(VpiClassMemberFullName(/*is_static=*/true, "top", "Packet", "Id"),
            "top.Packet::Id");
  // A static member with no enclosing scope path is just "Class::member".
  EXPECT_EQ(VpiClassMemberFullName(/*is_static=*/true, "", "Packet", "Id"),
            "Packet::Id");
}

// D26: vpiParent returns the first qualifying prefix scanning rightmost to
// leftmost, or NULL when none qualifies.
TEST(VariableModel, ParentReturnsFirstQualifyingPrefix) {
  VpiObject inner_index;  // a bare index strip - does not qualify
  VpiObject struct_var;
  std::vector<VpiParentPrefix> prefixes(2);
  prefixes[0].qualifies = false;
  prefixes[0].handle = &inner_index;
  prefixes[1].qualifies = true;
  prefixes[1].handle = &struct_var;
  EXPECT_EQ(VpiVariableParent(prefixes), &struct_var);

  // No qualifying prefix -> NULL.
  std::vector<VpiParentPrefix> none(1);
  none[0].qualifies = false;
  none[0].handle = &inner_index;
  EXPECT_EQ(VpiVariableParent(none), nullptr);
  EXPECT_EQ(VpiVariableParent({}), nullptr);
}

// D26: among nested array prefixes, vpiParent reports the largest (outermost)
// containing array.
TEST(VariableModel, LargestContainingArrayIsOutermost) {
  VpiObject innermost;  // e.g. mda[6][8][1]
  VpiObject outermost;  // e.g. mda[6][8]
  std::vector<VpiHandle> nested = {&innermost, &outermost};
  EXPECT_EQ(VpiLargestContainingArray(nested), &outermost);
  EXPECT_EQ(VpiLargestContainingArray({}), nullptr);
}

// D27: vpiConstantSelect is TRUE for a static-lifetime variable with no parent,
// or a select with all-constant indices over static-bound members; FALSE
// otherwise.
TEST(VariableModel, ConstantSelectRules) {
  VpiConstantSelectQuery q;

  q = {};
  q.has_static_lifetime = true;
  q.has_parent = false;
  EXPECT_TRUE(VpiConstantSelect(q));

  // Static lifetime but with a parent -> falls to the index/element test.
  q = {};
  q.has_static_lifetime = true;
  q.has_parent = true;
  q.all_indices_constant = true;
  q.all_elements_static_members = true;
  EXPECT_TRUE(VpiConstantSelect(q));

  // A non-constant index defeats it.
  q.all_indices_constant = false;
  EXPECT_FALSE(VpiConstantSelect(q));

  // A non-static-bound element defeats it.
  q.all_indices_constant = true;
  q.all_elements_static_members = false;
  EXPECT_FALSE(VpiConstantSelect(q));
}

// D28: vpiName excludes struct/union/class-var prefixes; vpiDecompile includes
// them without the top scope; vpiFullName adds the top scope. The object's own
// index/slice appears in all three.
TEST(VariableModel, NameDecompileFullNameForStructMember) {
  VpiVariableNameParts parts;
  parts.top_scope = "top";
  parts.member_prefixes = {"str1", "inner1"};
  parts.member = "j1";

  EXPECT_EQ(VpiVariableName(parts), "j1");
  EXPECT_EQ(VpiVariableDecompile(parts), "str1.inner1.j1");
  EXPECT_EQ(VpiVariableFullName(parts), "top.str1.inner1.j1");
}

// D28: an indexed element carries its index/slice in all three name forms.
TEST(VariableModel, NameFormsIncludeOwnIndexSuffix) {
  VpiVariableNameParts arr;
  arr.top_scope = "top";
  arr.member = "arr1";
  arr.index_suffix = "[1][9]";
  EXPECT_EQ(VpiVariableName(arr), "arr1[1][9]");
  EXPECT_EQ(VpiVariableDecompile(arr), "arr1[1][9]");
  EXPECT_EQ(VpiVariableFullName(arr), "top.arr1[1][9]");

  VpiVariableNameParts vec;
  vec.top_scope = "top";
  vec.member_prefixes = {"str1"};
  vec.member = "vec";
  vec.index_suffix = "[5]";
  EXPECT_EQ(VpiVariableName(vec), "vec[5]");
  EXPECT_EQ(VpiVariableDecompile(vec), "str1.vec[5]");
  EXPECT_EQ(VpiVariableFullName(vec), "top.str1.vec[5]");
}

}  // namespace
}  // namespace delta
