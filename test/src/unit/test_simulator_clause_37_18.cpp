#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.18 Packed array variables: the VPI object model for a vpiPackedArrayVar, a
// packed array of packed struct var, union var, or enum var objects. The
// clause's own normative details are exercised here:
//   detail 1 - vpiVector is always TRUE for a packed array var (carried by the
//              §37.17 variable helpers; observed here from §37.18's standpoint);
//   detail 2 - vpiSize is the number of bits in the packed array, not the number
//              of element objects (also a §37.17 size rule, observed here);
//   detail 3 - vpiElement reaches the subelements one dimension level at a time,
//              and they are themselves packed array vars for a multidimensioned
//              array;
//   detail 4 - vpiPackedArrayMember is TRUE for an element whose vpiParent is a
//              packed array var;
//   detail 5 - vpiStructUnionMember is TRUE only for a packed array var that is a
//              direct member of a struct/union var, FALSE for its subelements
//              (carried by the §37.17 helper, observed here);
//   detail 6 - vpi_iterate(vpiIndex, ...) reaches a subelement's index
//              expressions, beginning with its own index and working outward.
// The vpiPacked/vpiConstantSelect properties and the vpiParent edge are owned by
// the generic machinery and §37.17/§37.26, the cited dependencies.

// Walk an iterator to completion, collecting every object it yields in order.
std::vector<VpiHandle> Collect(VpiContext& ctx, VpiHandle iterator) {
  std::vector<VpiHandle> objects;
  if (!iterator) return objects;
  while (VpiHandle next = ctx.Scan(iterator)) objects.push_back(next);
  return objects;
}

// Detail 3: vpiElement on a packed array variable returns its subelements - here
// the leaf-level struct vars - skipping a child that is not an element kind, and
// preserving their declaration order.
TEST(PackedArrayVarModel, ElementIterationReachesSubelementsOneLevel) {
  VpiContext ctx;

  VpiObject member0;
  member0.type = vpiStructVar;
  VpiObject typespec;  // not an element kind: must be skipped
  typespec.type = vpiTypespec;
  VpiObject member1;
  member1.type = vpiStructVar;

  VpiObject pavar;
  pavar.type = vpiPackedArrayVar;
  pavar.children = {&member0, &typespec, &member1};

  std::vector<VpiHandle> elems = Collect(ctx, ctx.Iterate(vpiElement, &pavar));
  ASSERT_EQ(elems.size(), 2u);
  EXPECT_EQ(elems[0], &member0);
  EXPECT_EQ(elems[1], &member1);
}

// Detail 3: for a multidimensioned packed array, vpiElement retrieves elements
// that are themselves packed array vars (the leftmost packed range removed), one
// dimension level at a time.
TEST(PackedArrayVarModel, ElementIterationReachesPackedArrayVarsForMultiDim) {
  VpiContext ctx;

  VpiObject sub0;
  sub0.type = vpiPackedArrayVar;
  VpiObject sub1;
  sub1.type = vpiPackedArrayVar;
  VpiObject sub2;
  sub2.type = vpiPackedArrayVar;

  VpiObject pavar;
  pavar.type = vpiPackedArrayVar;
  pavar.children = {&sub0, &sub1, &sub2};

  std::vector<VpiHandle> elems = Collect(ctx, ctx.Iterate(vpiElement, &pavar));
  ASSERT_EQ(elems.size(), 3u);
  EXPECT_EQ(elems[0], &sub0);
  EXPECT_EQ(elems[1], &sub1);
  EXPECT_EQ(elems[2], &sub2);
}

// Detail 3 (boundary): the vpiElement relation is special only for a packed
// array var. A struct var that happens to carry children exposes no vpiElement
// iteration, so the iterator is NULL.
TEST(PackedArrayVarModel, ElementIterationIsNullForNonPackedArrayVar) {
  VpiContext ctx;

  VpiObject child;
  child.type = vpiStructVar;
  VpiObject struct_var;
  struct_var.type = vpiStructVar;
  struct_var.children = {&child};

  EXPECT_EQ(ctx.Iterate(vpiElement, &struct_var), nullptr);
}

// Detail 6: vpiIndex on a packed array var subelement returns its index
// expressions, beginning with the subelement's own index and working outward -
// the right-to-left textual order in which they are stored.
TEST(PackedArrayVarModel, IndexIterationReachesSubelementIndicesRightToLeft) {
  VpiContext ctx;

  VpiObject own_index;  // the subelement's own (rightmost) index
  own_index.type = vpiConstant;
  VpiObject outer_index;  // the next index working outward
  outer_index.type = vpiConstant;

  VpiObject subelement;
  subelement.type = vpiPackedArrayVar;
  subelement.children = {&own_index, &outer_index};

  std::vector<VpiHandle> indices =
      Collect(ctx, ctx.Iterate(vpiIndex, &subelement));
  ASSERT_EQ(indices.size(), 2u);
  EXPECT_EQ(indices[0], &own_index);
  EXPECT_EQ(indices[1], &outer_index);
}

// Detail 6: a packed array var that is not an element within an enclosing array
// has no index expressions, so iterating vpiIndex returns NULL.
TEST(PackedArrayVarModel, IndexIterationIsNullWhenNotAnArrayElement) {
  VpiContext ctx;

  VpiObject pavar;
  pavar.type = vpiPackedArrayVar;
  EXPECT_EQ(ctx.Iterate(vpiIndex, &pavar), nullptr);
}

// Details 3 and 6 select disjoint targets: when a packed array var carries both
// a struct-var subelement and an index expression, vpiElement reaches only the
// subelement and vpiIndex reaches only the index - the two special relations do
// not cross-contaminate.
TEST(PackedArrayVarModel, ElementAndIndexRelationsSelectDistinctTargets) {
  VpiContext ctx;

  VpiObject member;
  member.type = vpiStructVar;
  VpiObject index;
  index.type = vpiConstant;

  VpiObject pavar;
  pavar.type = vpiPackedArrayVar;
  pavar.children = {&member, &index};

  std::vector<VpiHandle> elems = Collect(ctx, ctx.Iterate(vpiElement, &pavar));
  ASSERT_EQ(elems.size(), 1u);
  EXPECT_EQ(elems[0], &member);

  std::vector<VpiHandle> indices = Collect(ctx, ctx.Iterate(vpiIndex, &pavar));
  ASSERT_EQ(indices.size(), 1u);
  EXPECT_EQ(indices[0], &index);
}

// Detail 4: vpiPackedArrayMember is TRUE for a struct var, union var, enum var,
// or packed array var whose vpiParent is a packed array var, and FALSE for an
// element with any other parent (or no parent at all).
TEST(PackedArrayVarModel, PackedArrayMemberTrueWhenParentIsPackedArrayVar) {
  VpiObject pavar;
  pavar.type = vpiPackedArrayVar;

  for (int kind :
       {vpiStructVar, vpiUnionVar, vpiEnumVar, vpiPackedArrayVar}) {
    VpiObject element;
    element.type = kind;
    element.parent = &pavar;
    EXPECT_TRUE(VpiVariableIsPackedArrayMember(&element)) << "kind=" << kind;
  }

  // A non-packed-array parent does not confer membership.
  VpiObject struct_parent;
  struct_parent.type = vpiStructVar;
  VpiObject member;
  member.type = vpiStructVar;
  member.parent = &struct_parent;
  EXPECT_FALSE(VpiVariableIsPackedArrayMember(&member));

  // A packed-array parent with an element kind outside the four is not a member.
  VpiObject scalar;
  scalar.type = vpiBitVar;
  scalar.parent = &pavar;
  EXPECT_FALSE(VpiVariableIsPackedArrayMember(&scalar));

  // A top-level variable with no vpiParent prefix is not a packed array member.
  VpiObject parentless;
  parentless.type = vpiPackedArrayVar;
  EXPECT_FALSE(VpiVariableIsPackedArrayMember(&parentless));

  // A null handle is handled safely and is not a member.
  EXPECT_FALSE(VpiVariableIsPackedArrayMember(nullptr));
}

// Detail 5: vpiStructUnionMember is TRUE for a packed array var that is a direct
// member of a struct or union var, and FALSE for a subelement reached by the
// vpiElement iterator (whose parent is a packed array var). The distinction is
// carried by the §37.17 helper and observed here for the packed-array-var case.
TEST(PackedArrayVarModel, StructUnionMemberDistinguishesDirectMembersFromSubs) {
  VpiObject struct_var;
  struct_var.type = vpiStructVar;
  VpiObject direct_member;
  direct_member.type = vpiPackedArrayVar;
  direct_member.parent = &struct_var;
  EXPECT_TRUE(VpiVariableIsStructUnionMember(&direct_member));

  VpiObject packed_parent;
  packed_parent.type = vpiPackedArrayVar;
  VpiObject subelement;
  subelement.type = vpiPackedArrayVar;
  subelement.parent = &packed_parent;
  EXPECT_FALSE(VpiVariableIsStructUnionMember(&subelement));
}

// Detail 2: vpiSize for a packed array var is the number of bits in the packed
// array, not the count of its struct/union/enum var elements. Observed through
// the §37.17 size helper, which routes a packed array var to its bit width.
TEST(PackedArrayVarModel, SizeIsBitsNotElementCount) {
  VpiVariableSizeQuery q;
  q.var_type = vpiPackedArrayVar;
  q.bit_width = 24;          // e.g. three 8-bit elements
  q.array_element_count = 3;  // the element count must not be reported
  EXPECT_EQ(VpiVariableSize(q), 24);
}

// Detail 1: vpiVector is always TRUE for a packed array var (and it is not a
// scalar). Observed through the §37.17 scalar/vector helpers.
TEST(PackedArrayVarModel, VectorAlwaysTrueForPackedArrayVar) {
  VpiScalarVectorQuery q;
  q.var_type = vpiPackedArrayVar;
  EXPECT_TRUE(VpiVariableVector(q));
  EXPECT_FALSE(VpiVariableScalar(q));
}

}  // namespace
}  // namespace delta
