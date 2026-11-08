#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

std::vector<VpiHandle> Collect(VpiContext& ctx, VpiHandle iterator) {
  std::vector<VpiHandle> objects;
  if (!iterator) return objects;
  while (VpiHandle next = ctx.Scan(iterator)) objects.push_back(next);
  return objects;
}

TEST(PackedArrayVarModel, ElementIterationReachesSubelementsOneLevel) {
  VpiContext ctx;

  VpiObject member0;
  member0.type = vpiStructVar;
  VpiObject typespec;
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

TEST(PackedArrayVarModel, ElementIterationIsNullForNonPackedArrayVar) {
  VpiContext ctx;

  VpiObject child;
  child.type = vpiStructVar;
  VpiObject struct_var;
  struct_var.type = vpiStructVar;
  struct_var.children = {&child};

  EXPECT_EQ(ctx.Iterate(vpiElement, &struct_var), nullptr);
}

TEST(PackedArrayVarModel, IndexIterationReachesSubelementIndicesRightToLeft) {
  VpiContext ctx;

  VpiObject own_index;
  own_index.type = vpiConstant;
  VpiObject outer_index;
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

TEST(PackedArrayVarModel, IndexIterationIsNullWhenNotAnArrayElement) {
  VpiContext ctx;

  VpiObject pavar;
  pavar.type = vpiPackedArrayVar;
  EXPECT_EQ(ctx.Iterate(vpiIndex, &pavar), nullptr);
}

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

TEST(PackedArrayVarModel, PackedArrayMemberTrueWhenParentIsPackedArrayVar) {
  VpiObject pavar;
  pavar.type = vpiPackedArrayVar;

  for (int kind : {vpiStructVar, vpiUnionVar, vpiEnumVar, vpiPackedArrayVar}) {
    VpiObject element;
    element.type = kind;
    element.parent = &pavar;
    EXPECT_TRUE(VpiVariableIsPackedArrayMember(&element)) << "kind=" << kind;
  }

  VpiObject struct_parent;
  struct_parent.type = vpiStructVar;
  VpiObject member;
  member.type = vpiStructVar;
  member.parent = &struct_parent;
  EXPECT_FALSE(VpiVariableIsPackedArrayMember(&member));

  VpiObject scalar;
  scalar.type = vpiBitVar;
  scalar.parent = &pavar;
  EXPECT_FALSE(VpiVariableIsPackedArrayMember(&scalar));

  VpiObject parentless;
  parentless.type = vpiPackedArrayVar;
  EXPECT_FALSE(VpiVariableIsPackedArrayMember(&parentless));

  EXPECT_FALSE(VpiVariableIsPackedArrayMember(nullptr));
}

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

TEST(PackedArrayVarModel, SizeIsBitsNotElementCount) {
  VpiVariableSizeQuery q;
  q.var_type = vpiPackedArrayVar;
  q.bit_width = 24;
  q.array_element_count = 3;
  EXPECT_EQ(VpiVariableSize(q), 24);
}

TEST(PackedArrayVarModel, VectorAlwaysTrueForPackedArrayVar) {
  VpiScalarVectorQuery q;
  q.var_type = vpiPackedArrayVar;
  EXPECT_TRUE(VpiVariableVector(q));
  EXPECT_FALSE(VpiVariableScalar(q));
}

TEST(PackedArrayVarPublic, PackedIsAlwaysTrueForAPackedArrayAndItsElements) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject array;
  array.type = vpiPackedArrayVar;
  VpiObject element;
  element.type = vpiStructVar;
  element.parent = &array;
  array.children = {&element};

  EXPECT_EQ(vpi_get(vpiPacked, VpiHandleOf(&array)), 1);
  EXPECT_EQ(vpi_get(vpiPacked, VpiHandleOf(&element)), 1);

  SetGlobalVpiContext(nullptr);
}

TEST(PackedArrayVarPublic, PackedStillReportsTheFlagForAnythingElse) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject unpacked;
  unpacked.type = vpiStructVar;
  EXPECT_EQ(vpi_get(vpiPacked, VpiHandleOf(&unpacked)), 0);

  VpiObject packed;
  packed.type = vpiStructVar;
  packed.packed = true;
  EXPECT_EQ(vpi_get(vpiPacked, VpiHandleOf(&packed)), 1);

  SetGlobalVpiContext(nullptr);
}

TEST(PackedArrayVarPublic, ASubelementReachesThePackedArrayItBelongsTo) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject array;
  array.type = vpiPackedArrayVar;
  VpiObject element;
  element.type = vpiEnumVar;
  element.parent = &array;
  array.children = {&element};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, VpiHandleOf(&element))), &array);

  VpiObject loose;
  loose.type = vpiEnumVar;
  EXPECT_EQ(vpi_handle(vpiParent, VpiHandleOf(&loose)), nullptr);

  SetGlobalVpiContext(nullptr);
}

class PackedArrayVarsOfARun : public VpiDesignRun {
 protected:
  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }
};

TEST_F(PackedArrayVarsOfARun, AStructVarWithAPackedDimensionIsAPackedArrayVar) {
  Run("module top;\n"
      "  typedef struct packed { int i1; bit [3:0] bvec; } pst;\n"
      "  pst [0:1][1:0] pavar1;\n"
      "  initial pavar1 = {32'd1, 4'h2, 32'd3, 4'h4, 32'd5, 4'h6, 32'd7, "
      "4'h8};\n"
      "endmodule\n");
  vpiHandle pavar1 = By("top.pavar1");
  ASSERT_NE(pavar1, nullptr);
  EXPECT_EQ(vpi_get(vpiType, pavar1), vpiPackedArrayVar);
  EXPECT_EQ(vpi_get(vpiSize, pavar1), 4 * 36);
  const std::vector<vpiHandle> kRows = ObjectsOf(vpiElement, pavar1);
  ASSERT_EQ(kRows.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kRows[1]), vpiPackedArrayVar);
  EXPECT_STREQ(vpi_get_str(vpiName, kRows[1]), "pavar1[1]");
  EXPECT_EQ(vpi_get(vpiSize, kRows[1]), 2 * 36);
  const std::vector<vpiHandle> kLeaves = ObjectsOf(vpiElement, kRows[1]);
  ASSERT_EQ(kLeaves.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kLeaves[0]), vpiStructVar);
  EXPECT_STREQ(vpi_get_str(vpiFullName, kLeaves[0]), "top.pavar1[1][1]");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, kLeaves[0])),
            VpiObjectOf(pavar1));
  EXPECT_EQ(vpi_get(vpiPackedArrayMember, kLeaves[0]), 1);
  EXPECT_EQ(vpi_get(vpiPackedArrayMember, pavar1), 0);
  EXPECT_EQ(IntOf(Named(vpiMember, kLeaves[0], "bvec")), 6);
  EXPECT_EQ(IntOf(Named(vpiMember, kLeaves[1], "i1")), 7);
}

TEST_F(PackedArrayVarsOfARun, AnEnumOrUnionVarWithAPackedDimensionIsOne) {
  Run("module top;\n"
      "  typedef enum logic [1:0] { A, B, C } et;\n"
      "  typedef union packed { logic [3:0] a; bit [3:0] b; } ut;\n"
      "  et [2:0] e; ut [1:0] u;\n"
      "endmodule\n");
  vpiHandle e = By("top.e");
  ASSERT_NE(e, nullptr);
  EXPECT_EQ(vpi_get(vpiType, e), vpiPackedArrayVar);
  const std::vector<vpiHandle> kLeaves = ObjectsOf(vpiElement, e);
  ASSERT_EQ(kLeaves.size(), 3U);
  EXPECT_EQ(vpi_get(vpiType, kLeaves[0]), vpiEnumVar);
  EXPECT_STREQ(vpi_get_str(vpiName, kLeaves[0]), "e[2]");
  vpiHandle u = By("top.u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(vpi_get(vpiType, u), vpiPackedArrayVar);
  const std::vector<vpiHandle> kUnions = ObjectsOf(vpiElement, u);
  ASSERT_EQ(kUnions.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kUnions[0]), vpiUnionVar);
  EXPECT_EQ(NamesOf(vpiMember, kUnions[0]),
            (std::vector<std::string>{"a", "b"}));
}

TEST_F(PackedArrayVarsOfARun, APackageStructsPackedArrayVarHasMembers) {
  Run("package pk;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } ps_t;\n"
      "endpackage\n"
      "module top;\n"
      "  pk::ps_t [1:0] pv;\n"
      "  initial pv = 16'h1234;\n"
      "endmodule\n");
  const std::vector<vpiHandle> kLeaves = ObjectsOf(vpiElement, By("top.pv"));
  ASSERT_EQ(kLeaves.size(), 2U);
  EXPECT_EQ(NamesOf(vpiMember, kLeaves[0]),
            (std::vector<std::string>{"a", "b"}));
  EXPECT_EQ(IntOf(Named(vpiMember, kLeaves[0], "a")), 1);
  EXPECT_EQ(IntOf(Named(vpiMember, kLeaves[1], "b")), 4);
}

TEST_F(PackedArrayVarsOfARun, AnInlineStructsPackedArrayVarHasMembers) {
  Run("module top;\n"
      "  struct packed { logic [3:0] a; logic [3:0] b; } [1:0] v;\n"
      "  initial v = 16'h1234;\n"
      "endmodule\n");
  vpiHandle v = By("top.v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(vpi_get(vpiType, v), vpiPackedArrayVar);
  const std::vector<vpiHandle> kLeaves = ObjectsOf(vpiElement, v);
  ASSERT_EQ(kLeaves.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kLeaves[0]), vpiStructVar);
  EXPECT_EQ(NamesOf(vpiMember, kLeaves[0]),
            (std::vector<std::string>{"a", "b"}));
  EXPECT_EQ(IntOf(Named(vpiMember, kLeaves[0], "a")), 1);
  EXPECT_EQ(IntOf(Named(vpiMember, kLeaves[1], "b")), 4);
}

}  // namespace
}  // namespace delta
