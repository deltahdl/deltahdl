#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(VariableModel, BackwardCompatibilityKindEquivalences) {
  EXPECT_EQ(vpiVarBit, vpiRegBit);
  EXPECT_TRUE(VpiIsLogicVarType(vpiLogicVar));
  EXPECT_TRUE(VpiIsLogicVarType(vpiReg));
  EXPECT_TRUE(VpiIsArrayVarType(vpiArrayVar));
  EXPECT_TRUE(VpiIsArrayVarType(vpiRegArray));
  EXPECT_FALSE(VpiIsLogicVarType(vpiBitVar));
  EXPECT_FALSE(VpiIsArrayVarType(vpiStructVar));
}

TEST(VariableModel, ArrayVarRequiresAtLeastOneUnpackedRange) {
  EXPECT_TRUE(VpiIsArrayVar(1));
  EXPECT_TRUE(VpiIsArrayVar(3));
  EXPECT_FALSE(VpiIsArrayVar(0));
}

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

  EXPECT_EQ(VpiRangeLeftRange(ranges[0]), &l0);
  EXPECT_EQ(VpiRangeRightRange(ranges[0]), &r0);
  EXPECT_EQ(VpiRangeSize(ranges[0]), 4);

  EXPECT_EQ(VpiRangeLeftRange(ranges[1]), nullptr);
  EXPECT_EQ(VpiRangeSize(ranges[1]), 0);
  EXPECT_EQ(VpiRangeRightRange(ranges[2]), nullptr);
  EXPECT_EQ(VpiRangeSize(ranges[2]), 0);
  EXPECT_EQ(VpiRangeLeftRange(ranges[3]), nullptr);
  EXPECT_EQ(VpiRangeSize(ranges[3]), 0);
}

TEST(VariableModel, RangeIterationDropsImplicitElementRanges) {
  VpiObject l;
  VpiObject r;
  std::vector<VpiArrayDimension> dims(2);
  dims[0].kind = VpiDimensionKind::kPacked;
  dims[0].left_expr = &l;
  dims[0].right_expr = &r;
  dims[0].size = 8;
  dims[1].kind = VpiDimensionKind::kPacked;
  dims[1].implicit_element_range = true;

  std::vector<VpiRangeDesc> ranges = VpiArrayVarRanges(dims);
  ASSERT_EQ(ranges.size(), 1u);
  EXPECT_EQ(VpiRangeLeftRange(ranges[0]), &l);
}

TEST(VariableModel, LeftRightRangeReportLeftmostDimensionBounds) {
  VpiObject l;
  VpiObject r;
  std::vector<VpiArrayDimension> dims(2);
  dims[0].kind = VpiDimensionKind::kPacked;
  dims[0].left_expr = &l;
  dims[0].right_expr = &r;
  dims[1].kind = VpiDimensionKind::kPacked;

  EXPECT_EQ(VpiVariableLeftRange(dims, true), &l);
  EXPECT_EQ(VpiVariableRightRange(dims, true), &r);
}

TEST(VariableModel, LeftRightRangeReportLeftmostUnpackedDimensionBounds) {
  VpiObject l;
  VpiObject r;
  std::vector<VpiArrayDimension> dims(2);
  dims[0].kind = VpiDimensionKind::kFixedUnpacked;
  dims[0].left_expr = &l;
  dims[0].right_expr = &r;
  dims[0].size = 4;
  dims[1].kind = VpiDimensionKind::kFixedUnpacked;

  EXPECT_EQ(VpiVariableLeftRange(dims, true), &l);
  EXPECT_EQ(VpiVariableRightRange(dims, true), &r);
}

TEST(VariableModel, LeftRightRangeNullForNoMembersOrEmptyRange) {
  VpiObject l;
  VpiObject r;
  std::vector<VpiArrayDimension> dims(1);
  dims[0].kind = VpiDimensionKind::kFixedUnpacked;
  dims[0].left_expr = &l;
  dims[0].right_expr = &r;

  EXPECT_EQ(VpiVariableLeftRange(dims, false), nullptr);
  EXPECT_EQ(VpiVariableRightRange(dims, false), nullptr);

  std::vector<VpiArrayDimension> assoc(1);
  assoc[0].kind = VpiDimensionKind::kAssoc;
  EXPECT_EQ(VpiVariableLeftRange(assoc, true), nullptr);
  EXPECT_EQ(VpiVariableRightRange(assoc, true), nullptr);

  EXPECT_EQ(VpiVariableLeftRange({}, true), nullptr);
}

TEST(VariableModel, InitializationExpressionReachedThroughExpr) {
  VpiObject init;
  VpiObject var;
  var.decl_facts.init_expr = &init;
  EXPECT_EQ(VpiVariableInitExpr(&var), &init);

  VpiObject typespec;
  VpiObject uninitialized;
  uninitialized.children.push_back(&typespec);
  EXPECT_EQ(VpiVariableInitExpr(&uninitialized), nullptr);
  EXPECT_EQ(VpiVariableInitExpr(nullptr), nullptr);
}

TEST(VariableModel, VarSelectSingleIndexIsTheInnermost) {
  VpiObject i0;
  VpiObject i1;
  std::vector<VpiHandle> indices = {&i0, &i1};
  EXPECT_EQ(VpiSelectSingleIndex(indices), &i0);
  EXPECT_EQ(VpiSelectSingleIndex({}), nullptr);
}

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
  q.var_type = vpiLogicVar;
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
  q.var_type = vpiStructVar;
  q.packed = false;
  q.field_count = 4;
  EXPECT_EQ(VpiVariableSize(q), 4);

  q = {};
  q.var_type = vpiStructVar;
  q.packed = true;
  q.bit_width = 17;
  EXPECT_EQ(VpiVariableSize(q), 17);

  q = {};
  q.var_type = vpiUnionVar;
  q.packed = false;
  q.field_count = 2;
  EXPECT_EQ(VpiVariableSize(q), 2);

  q = {};
  q.var_type = vpiUnionVar;
  q.packed = true;
  q.bit_width = 9;
  EXPECT_EQ(VpiVariableSize(q), 9);

  q = {};
  q.var_type = vpiVarBit;
  EXPECT_EQ(VpiVariableSize(q), 1);
}

TEST(VariableModel, SizeForIntegerTypedAndPackedArrayKinds) {
  for (int kind : {vpiByteVar, vpiShortIntVar, vpiLongIntVar, vpiIntegerVar,
                   vpiTimeVar, vpiBitVar, vpiPackedArrayVar}) {
    VpiVariableSizeQuery q;
    q.var_type = kind;
    q.bit_width = 16;
    EXPECT_EQ(VpiVariableSize(q), 16) << "kind=" << kind;
  }
}

TEST(VariableModel, VarSelectSizeIsBitCount) {
  VpiVariableSizeQuery q;
  q.var_type = vpiVarSelect;
  q.bit_width = 12;
  EXPECT_EQ(VpiVariableSize(q), 12);
}

TEST(VariableModel, SizeIsZeroWhenUndefined) {
  VpiVariableSizeQuery q;
  q.var_type = vpiChandleVar;
  EXPECT_EQ(VpiVariableSize(q), 0);
}

TEST(VariableModel, ValuePropertyAvailability) {
  EXPECT_FALSE(VpiVariableHasValueProperty(vpiArrayVar, false));
  EXPECT_FALSE(VpiVariableHasValueProperty(vpiClassVar, false));
  EXPECT_FALSE(VpiVariableHasValueProperty(vpiVirtualInterfaceVar, false));
  EXPECT_FALSE(VpiVariableHasValueProperty(vpiStructVar, false));
  EXPECT_TRUE(VpiVariableHasValueProperty(vpiStructVar, true));
  EXPECT_FALSE(VpiVariableHasValueProperty(vpiUnionVar, false));
  EXPECT_TRUE(VpiVariableHasValueProperty(vpiUnionVar, true));
  EXPECT_TRUE(VpiVariableHasValueProperty(vpiLogicVar, false));
  EXPECT_TRUE(VpiVariableHasValueProperty(vpiIntVar, false));
}

TEST(VariableModel, BitIteratorApplicability) {
  EXPECT_TRUE(VpiBitIteratorApplies(vpiLogicVar, false));
  EXPECT_TRUE(VpiBitIteratorApplies(vpiBitVar, false));
  EXPECT_TRUE(VpiBitIteratorApplies(vpiPackedArrayVar, false));
  EXPECT_TRUE(VpiBitIteratorApplies(vpiStructVar, true));
  EXPECT_FALSE(VpiBitIteratorApplies(vpiStructVar, false));
  EXPECT_TRUE(VpiBitIteratorApplies(vpiUnionVar, true));
  EXPECT_FALSE(VpiBitIteratorApplies(vpiUnionVar, false));
  EXPECT_FALSE(VpiBitIteratorApplies(vpiIntVar, false));
  EXPECT_FALSE(VpiBitIteratorApplies(vpiStringVar, false));
}

TEST(VariableModel, RandTypeDomain) {
  EXPECT_TRUE(VpiIsRandTypeValue(vpiRand));
  EXPECT_TRUE(VpiIsRandTypeValue(vpiRandC));
  EXPECT_TRUE(VpiIsRandTypeValue(vpiNotRand));
  EXPECT_FALSE(VpiIsRandTypeValue(0));
  EXPECT_FALSE(VpiIsRandTypeValue(99));
}

TEST(VariableModel, IsRandomizedReflectsActiveness) {
  EXPECT_TRUE(VpiIsRandomized(true));
  EXPECT_FALSE(VpiIsRandomized(false));
}

TEST(VariableModel, SizeChangeCallbackApplicability) {
  EXPECT_TRUE(VpiSizeChangeCallbackApplies(vpiDynamicArray, false));
  EXPECT_TRUE(VpiSizeChangeCallbackApplies(vpiAssocArray, false));
  EXPECT_TRUE(VpiSizeChangeCallbackApplies(vpiQueueArray, false));
  EXPECT_TRUE(VpiSizeChangeCallbackApplies(0, true));
  EXPECT_FALSE(VpiSizeChangeCallbackApplies(vpiStaticArray, false));
  EXPECT_FALSE(VpiSizeChangeCallbackApplies(0, false));
}

TEST(VariableModel, ArrayTypeDomain) {
  EXPECT_TRUE(VpiIsArrayTypeValue(vpiStaticArray));
  EXPECT_TRUE(VpiIsArrayTypeValue(vpiDynamicArray));
  EXPECT_TRUE(VpiIsArrayTypeValue(vpiAssocArray));
  EXPECT_TRUE(VpiIsArrayTypeValue(vpiQueueArray));
  EXPECT_FALSE(VpiIsArrayTypeValue(0));
}

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
  q.var_type = vpiUnionVar;
  q.packed = true;
  EXPECT_TRUE(VpiVariableVector(q));
  q.packed = false;
  EXPECT_FALSE(VpiVariableVector(q));
  EXPECT_FALSE(VpiVariableScalar(q));

  q = {};
  q.var_type = vpiStringVar;
  EXPECT_FALSE(VpiVariableScalar(q));
  EXPECT_FALSE(VpiVariableVector(q));
}

TEST(VariableModel, VectorForAllIntegerTypedKinds) {
  for (int kind : {vpiIntegerVar, vpiTimeVar, vpiShortIntVar, vpiIntVar,
                   vpiLongIntVar, vpiByteVar}) {
    VpiScalarVectorQuery q;
    q.var_type = kind;
    EXPECT_TRUE(VpiVariableVector(q)) << "kind=" << kind;
    EXPECT_FALSE(VpiVariableScalar(q)) << "kind=" << kind;
  }
}

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

TEST(VariableModel, VisibilityRules) {
  EXPECT_EQ(VpiVariableVisibility(false, vpiLocalVis), vpiPublicVis);
  EXPECT_EQ(VpiVariableVisibility(true, vpiPublicVis), vpiPublicVis);
  EXPECT_EQ(VpiVariableVisibility(true, vpiLocalVis), vpiLocalVis);
  EXPECT_EQ(VpiVariableVisibility(true, vpiProtectedVis), vpiProtectedVis);
}

TEST(VariableModel, ClassMemberFullName) {
  EXPECT_EQ(VpiClassMemberFullName(false, "top", "Packet", "Id"), "");
  EXPECT_EQ(VpiClassMemberFullName(true, "top", "Packet", "Id"),
            "top.Packet::Id");
  EXPECT_EQ(VpiClassMemberFullName(true, "", "Packet", "Id"), "Packet::Id");
}

TEST(VariableModel, ParentReturnsFirstQualifyingPrefix) {
  VpiObject inner_index;
  VpiObject struct_var;
  std::vector<VpiParentPrefix> prefixes(2);
  prefixes[0].qualifies = false;
  prefixes[0].handle = &inner_index;
  prefixes[1].qualifies = true;
  prefixes[1].handle = &struct_var;
  EXPECT_EQ(VpiVariableParent(prefixes), &struct_var);

  std::vector<VpiParentPrefix> none(1);
  none[0].qualifies = false;
  none[0].handle = &inner_index;
  EXPECT_EQ(VpiVariableParent(none), nullptr);
  EXPECT_EQ(VpiVariableParent({}), nullptr);
}

TEST(VariableModel, LargestContainingArrayIsOutermost) {
  VpiObject innermost;
  VpiObject outermost;
  std::vector<VpiHandle> nested = {&innermost, &outermost};
  EXPECT_EQ(VpiLargestContainingArray(nested), &outermost);
  EXPECT_EQ(VpiLargestContainingArray({}), nullptr);
}

TEST(VariableModel, ConstantSelectRules) {
  VpiConstantSelectQuery q;

  q = {};
  q.has_static_lifetime = true;
  q.has_parent = false;
  EXPECT_TRUE(VpiConstantSelect(q));

  q = {};
  q.has_static_lifetime = true;
  q.has_parent = true;
  q.all_indices_constant = true;
  q.all_elements_static_members = true;
  EXPECT_TRUE(VpiConstantSelect(q));

  q.all_indices_constant = false;
  EXPECT_FALSE(VpiConstantSelect(q));

  q.all_indices_constant = true;
  q.all_elements_static_members = false;
  EXPECT_FALSE(VpiConstantSelect(q));
}

TEST(VariableModel, NameDecompileFullNameForStructMember) {
  VpiVariableNameParts parts;
  parts.top_scope = "top";
  parts.member_prefixes = {"str1", "inner1"};
  parts.member = "j1";

  EXPECT_EQ(VpiVariableName(parts), "j1");
  EXPECT_EQ(VpiVariableDecompile(parts), "str1.inner1.j1");
  EXPECT_EQ(VpiVariableFullName(parts), "top.str1.inner1.j1");
}

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

TEST(VariableModel, ScalarAndVectorOfABitAVariableAndAnotherKind) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  VpiObject bit;
  bit.type = vpiRegBit;
  EXPECT_EQ(vpi_get(vpiScalar, VpiHandleOf(&bit)), 1);
  EXPECT_EQ(vpi_get(vpiVector, VpiHandleOf(&bit)), 0);
  VpiObject var;
  var.type = vpiIntVar;
  EXPECT_EQ(vpi_get(vpiScalar, VpiHandleOf(&var)), 0);
  VpiObject scope;
  scope.type = vpiModule;
  EXPECT_EQ(vpi_get(vpiVector, VpiHandleOf(&scope)), 0);
  SetGlobalVpiContext(nullptr);
}

TEST(VariableModel, AStringVarWithNoStorageHasNoCharacters) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  VpiObject str;
  str.type = vpiStringVar;
  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(&str)), 0);
  SetGlobalVpiContext(nullptr);
}

TEST(VariableModel, EveryDrawnKindIsAVariable) {
  for (int type : {vpiShortRealVar, vpiRealVar, vpiShortIntVar, vpiLongIntVar,
                   vpiPackedArrayVar, vpiUnionVar, vpiEnumVar, vpiChandleVar}) {
    EXPECT_TRUE(VpiIsVariablesType(type)) << type;
  }
}

TEST(VariableModel, BitAndIndexedPartSelectsAreVariableSelects) {
  EXPECT_TRUE(VpiIsVariableSelectType(vpiBitSelect));
  EXPECT_TRUE(VpiIsVariableSelectType(vpiIndexedPartSelect));
}

TEST(VariableModel, VisibilityOutsideAClassAndOfOtherKinds) {
  VpiObject loose;
  loose.type = vpiIntVar;
  EXPECT_EQ(VpiObjectVisibility(&loose), vpiPublicVis);
  VpiObject module;
  module.type = vpiModule;
  VpiObject member;
  member.type = vpiIntVar;
  member.parent = &module;
  EXPECT_EQ(VpiObjectVisibility(&member), vpiPublicVis);
  EXPECT_EQ(VpiObjectVisibility(&module), vpiUndefined);
}

TEST(VariableModel, AnAutomaticConstantSelectRestsOnItsIndices) {
  VpiConstantSelectQuery query;
  query.all_indices_constant = true;
  query.all_elements_static_members = true;
  EXPECT_TRUE(VpiConstantSelect(query));
}

TEST(VariableModel, AFullNameWithNoTopScopeIsTheDecompiledForm) {
  VpiVariableNameParts parts;
  parts.member = "m";
  parts.index_suffix = "[1]";
  EXPECT_EQ(VpiVariableFullName(parts), "m[1]");
}

}  // namespace
}  // namespace delta
