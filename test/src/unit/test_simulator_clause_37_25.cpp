#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.25 Typespec: a typespec object describes a type specification. These tests
// observe the production helpers in vpi.cpp that apply the clause's numbered
// "Details" - what vpiName/vpiTypedefAlias report (detail 1), which typespecs
// carry an index typespec (detail 2) and members (detail 3/4), what a member's
// type and default value are (detail 3/7), how vpiElemTypespec unwinds an array
// (detail 8), and how the figure's range relations route through §37.22 (details
// 9 and 10). The figure attributes with no numbered Detail (vpiTagged/vpiSoft/
// vpiPacked/vpiVector/vpiArrayType/vpiRandType) belong to §37.26 and §37.17.

// §37.25: the typespec class groups every "... typespec" node of the figure; a
// plain expression or variable object is not a typespec.
TEST(Typespec, TypespecClassMembership) {
  EXPECT_TRUE(VpiIsTypespecType(vpiEnumTypespec));
  EXPECT_TRUE(VpiIsTypespecType(vpiStructTypespec));
  EXPECT_TRUE(VpiIsTypespecType(vpiArrayTypespec));
  EXPECT_TRUE(VpiIsTypespecType(vpiPackedArrayTypespec));
  // Detail 11: an unresolved type parameter acts as a typespec.
  EXPECT_TRUE(VpiIsTypespecType(vpiTypeParameter));
  EXPECT_FALSE(VpiIsTypespecType(vpiConstant));
  EXPECT_FALSE(VpiIsTypespecType(vpiStructVar));
}

// D1: a typespec denoting a user-defined typedef reports that typedef's name.
TEST(Typespec, NameOfUserDefinedTypedef) {
  EXPECT_STREQ(VpiTypespecName(vpiEnumTypespec, /*denotes_user_typedef=*/true,
                               "colors", nullptr),
               "colors");
}

// D1: vpiName returns NULL for a SystemVerilog built-in type (no user typedef).
TEST(Typespec, NameOfBuiltInTypeIsNull) {
  EXPECT_EQ(VpiTypespecName(vpiIntTypespec, /*denotes_user_typedef=*/false,
                            nullptr, nullptr),
            nullptr);
}

// D1: a class typespec reports the class name even though it is not a typedef.
TEST(Typespec, NameOfClassTypespecIsClassName) {
  EXPECT_STREQ(VpiTypespecName(vpiClassTypespec, /*denotes_user_typedef=*/false,
                               nullptr, "my_class"),
               "my_class");
}

// D5: a typedef field defined inline rather than via a typedef declaration may
// have the empty string for its name; that empty name is still reported (not
// NULL, which is reserved for built-in types).
TEST(Typespec, NameOfInlineFieldMayBeEmpty) {
  const char* name = VpiTypespecName(
      vpiStructTypespec, /*denotes_user_typedef=*/true, "", nullptr);
  ASSERT_NE(name, nullptr);
  EXPECT_STREQ(name, "");
}

// D1: a typespec whose typedef aliases another typedef hands back a handle to the
// aliased typedef; the aliased typedef, not itself an alias, reports NULL. This
// mirrors the colors -> primary_colors example.
TEST(Typespec, TypedefAliasChain) {
  VpiObject primary_colors;
  EXPECT_EQ(VpiTypespecTypedefAlias(/*is_alias=*/true, &primary_colors),
            &primary_colors);
  EXPECT_EQ(VpiTypespecTypedefAlias(/*is_alias=*/false, nullptr), nullptr);
}

// D6: a type defined as an alias of another type inherits the other type's
// vpiType, so both the alias and the aliased typespec report the same type code,
// observed through the existing vpi_get(vpiType). The alias of a time typedef
// reports vpiTimeTypespec, not a distinct alias type.
TEST(Typespec, AliasInheritsUnderlyingType) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject aliased;  // the predefined "time" typespec
  aliased.type = vpiTimeTypespec;
  VpiObject my_time;  // typedef time my_time;
  my_time.type = vpiTimeTypespec;  // inherits the underlying type

  EXPECT_EQ(vpi_get(vpiType, &my_time), vpiTimeTypespec);
  EXPECT_EQ(vpi_get(vpiType, &aliased), vpi_get(vpiType, &my_time));

  SetGlobalVpiContext(nullptr);
}

// D2: vpiIndexTypespec exists only on an associative-array typespec and gives the
// key type.
TEST(Typespec, IndexTypespecOnAssociativeArray) {
  VpiObject key;
  EXPECT_EQ(VpiTypespecIndexTypespec(/*is_assoc_array_typespec=*/true,
                                     /*wildcard_index=*/false, &key),
            &key);
}

// D2: a wildcard index type has no index typespec.
TEST(Typespec, IndexTypespecNullForWildcardIndex) {
  VpiObject key;
  EXPECT_EQ(VpiTypespecIndexTypespec(/*is_assoc_array_typespec=*/true,
                                     /*wildcard_index=*/true, &key),
            nullptr);
}

// D2: a non-associative typespec carries no index typespec at all.
TEST(Typespec, IndexTypespecNullForNonAssociativeTypespec) {
  VpiObject key;
  EXPECT_EQ(VpiTypespecIndexTypespec(/*is_assoc_array_typespec=*/false,
                                     /*wildcard_index=*/false, &key),
            nullptr);
}

// D3: a struct typespec exposes its members through vpiTypespecMember; a union
// typespec does likewise.
TEST(Typespec, StructAndUnionExposeMembers) {
  VpiObject a;
  VpiObject b;
  std::vector<VpiHandle> members = {&a, &b};
  EXPECT_EQ(VpiTypespecMembers(vpiStructTypespec, members).size(), 2u);
  EXPECT_EQ(VpiTypespecMembers(vpiUnionTypespec, members).size(), 2u);
}

// D3: a typespec that is not a struct or union has no typespec members.
TEST(Typespec, NonStructTypespecHasNoMembers) {
  VpiObject a;
  std::vector<VpiHandle> members = {&a};
  EXPECT_TRUE(VpiTypespecMembers(vpiEnumTypespec, members).empty());
}

// D3: the typespec relation of a member indicates the member's type - its
// typespec child, distinct from any default-value expr child.
TEST(Typespec, MemberTypespecIsTheTypespecChild) {
  VpiObject member;
  VpiObject member_type;
  member_type.type = vpiIntTypespec;
  VpiObject default_value;
  default_value.type = vpiConstant;
  member.children = {&default_value, &member_type};

  EXPECT_EQ(VpiTypespecMemberTypespec(&member), &member_type);
}

// D4: vpiName of a typespec member is the member's own name, not the name of the
// member's type.
TEST(Typespec, MemberNameIsTheMembersOwnName) {
  VpiObject member;
  member.name = "a";
  EXPECT_STREQ(VpiTypespecMemberName(&member), "a");
}

// D7: the expr of a member is the member's explicit default value - its expr
// child (an object of the §37.59 expr class).
TEST(Typespec, MemberDefaultExprIsTheExprChild) {
  VpiObject member;
  VpiObject member_type;
  member_type.type = vpiIntTypespec;
  VpiObject default_value;
  default_value.type = vpiConstant;
  member.children = {&member_type, &default_value};

  EXPECT_EQ(VpiTypespecMemberDefaultExpr(&member), &default_value);
}

// D7: a member with no default value has no expr.
TEST(Typespec, MemberWithoutDefaultHasNoExpr) {
  VpiObject member;
  VpiObject member_type;
  member_type.type = vpiIntTypespec;
  member.children = {&member_type};

  EXPECT_EQ(VpiTypespecMemberDefaultExpr(&member), nullptr);
}

// D3 edge: a member whose children include no typespec object (only, say, a
// default-value expr) reports no member type rather than misreading the expr.
TEST(Typespec, MemberTypespecNullWhenNoTypespecChild) {
  VpiObject member;
  VpiObject default_value;
  default_value.type = vpiConstant;  // an expr, not a typespec
  member.children = {&default_value};

  EXPECT_EQ(VpiTypespecMemberTypespec(&member), nullptr);
}

// D3/D4/D7 error condition: the member relations tolerate a null member handle,
// reporting no type, no name, and no default expr rather than dereferencing it.
TEST(Typespec, MemberRelationsNullHandleSafe) {
  EXPECT_EQ(VpiTypespecMemberTypespec(nullptr), nullptr);
  EXPECT_EQ(VpiTypespecMemberName(nullptr), nullptr);
  EXPECT_EQ(VpiTypespecMemberDefaultExpr(nullptr), nullptr);
}

// D8: vpiElemTypespec unwinds one dimension at a time. While the typespec still
// has a range it hands back the element typespec (the next unwinding level);
// once no ranges remain it yields NULL. This walks the figure's arr example:
// a 4x3 unpacked array typespec -> ... -> base struct typespec.
TEST(Typespec, ElemTypespecUnwindsUntilNoRangesRemain) {
  VpiObject after_first_unwind;   // 3-element unpacked array typespec
  VpiObject base_struct;          // the non-array element, no ranges left

  // The outer typespec still has unpacked ranges, so unwinding yields the next
  // level.
  EXPECT_EQ(VpiTypespecElemTypespec(/*has_ranges=*/true, &after_first_unwind),
            &after_first_unwind);
  // The base struct typespec has no ranges, so vpiElemTypespec is NULL.
  EXPECT_EQ(VpiTypespecElemTypespec(/*has_ranges=*/false, &base_struct),
            nullptr);
}

// D8 edge: a multidimensional array typespec unwinds one level per call, walking
// the chain until the base element (no ranges) is reached and the next call
// yields NULL - the stepwise behavior of the figure's arr example.
TEST(Typespec, ElemTypespecUnwindsMultipleDimensionsStepwise) {
  VpiObject inner;  // the outer array with its leftmost range removed
  VpiObject base;   // the base element typespec, no ranges remaining

  // First call removes the leftmost range, exposing the inner level.
  EXPECT_EQ(VpiTypespecElemTypespec(/*has_ranges=*/true, &inner), &inner);
  // Next call unwinds the inner level's remaining range to the base element.
  EXPECT_EQ(VpiTypespecElemTypespec(/*has_ranges=*/true, &base), &base);
  // The base element has no ranges, so the unwinding terminates at NULL.
  EXPECT_EQ(VpiTypespecElemTypespec(/*has_ranges=*/false, nullptr), nullptr);
}

// D10: vpi_iterate(vpiRange, array_typespec) returns one range per declared
// dimension, leftmost to rightmost.
TEST(Typespec, RangeIterationYieldsOneRangePerDimension) {
  VpiObject l0, r0, l1, r1;
  std::vector<VpiArrayDimension> dims(2);
  dims[0].kind = VpiDimensionKind::kFixedUnpacked;
  dims[0].left_expr = &l0;
  dims[0].right_expr = &r0;
  dims[0].size = 4;
  dims[1].kind = VpiDimensionKind::kFixedUnpacked;
  dims[1].left_expr = &l1;
  dims[1].right_expr = &r1;
  dims[1].size = 3;

  std::vector<VpiRangeDesc> ranges = VpiTypespecRanges(dims);
  ASSERT_EQ(ranges.size(), 2u);
  EXPECT_EQ(VpiRangeLeftRange(ranges[0]), &l0);
  EXPECT_EQ(VpiRangeRightRange(ranges[1]), &r1);
}

// D10: a dynamic, associative, or queue dimension of the typespec contributes an
// empty range (§37.22).
TEST(Typespec, RangeIterationGivesEmptyRangeForUnboundedDimension) {
  VpiObject l, r;
  std::vector<VpiArrayDimension> dims(1);
  dims[0].kind = VpiDimensionKind::kAssoc;
  dims[0].left_expr = &l;
  dims[0].right_expr = &r;
  dims[0].size = 7;

  std::vector<VpiRangeDesc> ranges = VpiTypespecRanges(dims);
  ASSERT_EQ(ranges.size(), 1u);
  EXPECT_EQ(VpiRangeSize(ranges[0]), 0);
  EXPECT_EQ(VpiRangeLeftRange(ranges[0]), nullptr);
}

// D9: vpiLeftRange/vpiRightRange of a typespec report the bounds of the leftmost
// declared dimension (leftmost packed for a logic/bit/packed-array typespec,
// leftmost unpacked for an array typespec).
TEST(Typespec, LeftAndRightRangeUseLeftmostDimension) {
  VpiObject l0, r0, l1, r1;
  std::vector<VpiArrayDimension> dims(2);
  dims[0].left_expr = &l0;
  dims[0].right_expr = &r0;
  dims[1].left_expr = &l1;
  dims[1].right_expr = &r1;

  EXPECT_EQ(VpiTypespecLeftRange(dims), &l0);
  EXPECT_EQ(VpiTypespecRightRange(dims), &r0);
}

// D9: when the leftmost unpacked dimension corresponds to an empty range, both
// vpiLeftRange and vpiRightRange return NULL (§37.22).
TEST(Typespec, LeftAndRightRangeNullForEmptyLeftmostDimension) {
  VpiObject l, r;
  std::vector<VpiArrayDimension> dims(1);
  dims[0].kind = VpiDimensionKind::kDynamic;
  dims[0].left_expr = &l;
  dims[0].right_expr = &r;

  EXPECT_EQ(VpiTypespecLeftRange(dims), nullptr);
  EXPECT_EQ(VpiTypespecRightRange(dims), nullptr);
}

// D9: a typespec with no declared dimension has neither a left nor a right range.
TEST(Typespec, LeftAndRightRangeNullWhenNoDimensions) {
  std::vector<VpiArrayDimension> dims;
  EXPECT_EQ(VpiTypespecLeftRange(dims), nullptr);
  EXPECT_EQ(VpiTypespecRightRange(dims), nullptr);
}

// D11: in a context where the type parameter is unresolved, the type parameter
// itself acts as the typespec; once resolved, the resolved typespec stands in.
TEST(Typespec, UnresolvedTypeParameterActsAsTypespec) {
  VpiObject type_parameter;
  type_parameter.type = vpiTypeParameter;
  VpiObject resolved;
  resolved.type = vpiIntTypespec;

  EXPECT_EQ(VpiTypespecForTypeParameter(&type_parameter, nullptr),
            &type_parameter);
  EXPECT_EQ(VpiTypespecForTypeParameter(&type_parameter, &resolved), &resolved);
}

}  // namespace
}  // namespace delta
