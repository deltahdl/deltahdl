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

  static std::vector<std::string> ElementNamesOf(vpiHandle obj) {
    std::vector<std::string> names;
    for (vpiHandle element : ObjectsOf(vpiElement, obj)) {
      const char* name = vpi_get_str(vpiName, element);
      names.emplace_back(name == nullptr ? "<null>" : name);
    }
    return names;
  }

  static std::vector<int> RangeSizesOf(vpiHandle obj) {
    std::vector<int> sizes;
    for (vpiHandle range : ObjectsOf(vpiRange, obj)) {
      sizes.push_back(vpi_get(vpiSize, range));
    }
    return sizes;
  }

  static VpiObject* ParentOf(vpiHandle obj) {
    return VpiObjectOf(vpi_handle(vpiParent, obj));
  }

  static std::string TypespecNameOf(vpiHandle obj) {
    vpiHandle typespec = vpi_handle(vpiTypespec, obj);
    if (typespec == nullptr) return "<no typespec>";
    const char* name = vpi_get_str(vpiName, typespec);
    return name == nullptr ? "<null>" : name;
  }
};

constexpr const char* kStructTypedef =
    "  typedef struct packed { int i1; bit [3:0] bvec; } pst;\n";

constexpr const char* kEnumAndUnionTypedefs =
    "  typedef enum logic [1:0] { A, B, C } et;\n"
    "  typedef union packed { logic [3:0] a; bit [3:0] b; } ut;\n";

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
  EXPECT_EQ(vpi_get(vpiType, By("top.pv")), vpiPackedArrayVar);
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

TEST_F(PackedArrayVarsOfARun,
       AnAggregateWithNoPackedDimensionIsNoPackedArrayVar) {
  Run(std::string("module top;\n") + kStructTypedef + kEnumAndUnionTypedefs +
      "  pst s; et e; ut u;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, By("top.s")), vpiStructVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.e")), vpiEnumVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.u")), vpiUnionVar);
}

TEST_F(PackedArrayVarsOfARun,
       DISABLED_ATypedefsPackedDimensionsMakeAPackedArrayVar) {
  Run(std::string("module top;\n") + kStructTypedef + kEnumAndUnionTypedefs +
      "  typedef pst [1:0] sarr_t; typedef et [2:0] earr_t;\n"
      "  sarr_t sv; earr_t ev;\n"
      "endmodule\n");
  vpiHandle sv = By("top.sv");
  ASSERT_NE(sv, nullptr);
  EXPECT_EQ(vpi_get(vpiType, sv), vpiPackedArrayVar);
  EXPECT_EQ(KindsOf(vpiElement, sv),
            (std::vector<int>{vpiStructVar, vpiStructVar}));
  vpiHandle ev = By("top.ev");
  ASSERT_NE(ev, nullptr);
  EXPECT_EQ(vpi_get(vpiType, ev), vpiPackedArrayVar);
  EXPECT_EQ(KindsOf(vpiElement, ev),
            (std::vector<int>{vpiEnumVar, vpiEnumVar, vpiEnumVar}));
}

TEST_F(PackedArrayVarsOfARun, APackagesEnumOrUnionWithAPackedDimensionIsOne) {
  Run(std::string("package pk;\n") + kEnumAndUnionTypedefs +
      "endpackage\n"
      "module top; pk::ut [1:0] u; pk::et [1:0] e; endmodule\n");
  vpiHandle u = By("top.u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(vpi_get(vpiType, u), vpiPackedArrayVar);
  EXPECT_EQ(KindsOf(vpiElement, u),
            (std::vector<int>{vpiUnionVar, vpiUnionVar}));
  vpiHandle e = By("top.e");
  ASSERT_NE(e, nullptr);
  EXPECT_EQ(vpi_get(vpiType, e), vpiPackedArrayVar);
  EXPECT_EQ(KindsOf(vpiElement, e), (std::vector<int>{vpiEnumVar, vpiEnumVar}));
}

std::string PlacesDesign() {
  return "package t;\n"
         "  typedef struct packed { logic [3:0] a; } ps_t;\n"
         "endpackage\n"
         "package pkg; t::ps_t [1:0] pv; endpackage\n"
         "t::ps_t [1:0] uv;\n"
         "function automatic void uf(); t::ps_t [1:0] fv; endfunction\n"
         "interface ifc; t::ps_t [1:0] iv; endinterface\n"
         "program prg; t::ps_t [1:0] rv; endprogram\n"
         "module top; ifc i(); prg p();\n"
         "  class C; t::ps_t [1:0] cv; endclass\n"
         "  task run; t::ps_t [1:0] tv; endtask\n"
         "  initial begin : blk t::ps_t [1:0] bv; end\n"
         "  if (1) begin : g t::ps_t [1:0] gv; end\n"
         "endmodule\n";
}

TEST_F(PackedArrayVarsOfARun,
       DISABLED_APackageOrCompilationUnitDeclaresAPackedArrayVar) {
  Run(PlacesDesign());
  vpiHandle unit = Named(vpiPackage, nullptr, "$unit");
  ASSERT_NE(unit, nullptr);
  EXPECT_EQ(vpi_get(vpiType, Named(vpiVariables, By("pkg"), "pv")),
            vpiPackedArrayVar);
  EXPECT_EQ(vpi_get(vpiType, Named(vpiVariables, unit, "uv")),
            vpiPackedArrayVar);
}

TEST_F(PackedArrayVarsOfARun,
       AnInstanceOrGenerateBlockDeclaresAPackedArrayVar) {
  Run(PlacesDesign());
  EXPECT_EQ(vpi_get(vpiType, By("top.i.iv")), vpiPackedArrayVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.p.rv")), vpiPackedArrayVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.g.gv")), vpiPackedArrayVar);
}

TEST_F(PackedArrayVarsOfARun, DISABLED_AClassPropertyIsAPackedArrayVar) {
  Run(PlacesDesign());
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(defn, nullptr);
  EXPECT_EQ(vpi_get(vpiType, Named(vpiVariables, defn, "cv")),
            vpiPackedArrayVar);
}

TEST_F(PackedArrayVarsOfARun,
       DISABLED_ASubroutineOrNamedBlockDeclaresAPackedArrayVar) {
  Run(PlacesDesign());
  vpiHandle uf = Named(vpiTaskFunc, Named(vpiPackage, nullptr, "$unit"), "uf");
  ASSERT_NE(uf, nullptr);
  EXPECT_EQ(vpi_get(vpiType, Named(vpiVariables, uf, "fv")), vpiPackedArrayVar);
  vpiHandle run = Named(vpiTaskFunc, By("top"), "run");
  ASSERT_NE(run, nullptr);
  EXPECT_EQ(vpi_get(vpiType, Named(vpiVariables, run, "tv")),
            vpiPackedArrayVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.blk.bv")), vpiPackedArrayVar);
}

std::string ElementKindsDesign() {
  return std::string("module top;\n") + kStructTypedef + kEnumAndUnionTypedefs +
         "  pst [0:1][1:0] pavar1; et [2:0] e; ut [1:0] u;\n"
         "endmodule\n";
}

std::string AggregateMembersDesign() {
  return "module top;\n"
         "  typedef struct packed { logic [1:0] f; } el_t;\n"
         "  typedef struct packed { el_t [3:0] pa; logic b; } ps_t;\n"
         "  typedef union packed { el_t [3:0] pa; logic [7:0] w; } pu_t;\n"
         "  typedef struct { el_t [3:0] pa; int i; } us_t;\n"
         "  typedef union { el_t [3:0] pa; int i; } uu_t;\n"
         "  ps_t ps; pu_t pu; us_t us; uu_t uu; el_t [3:0] pa;\n"
         "endmodule\n";
}

TEST_F(PackedArrayVarsOfARun, EverySubelementIsAPackedArrayMember) {
  Run(ElementKindsDesign());
  const std::vector<vpiHandle> kRows = ObjectsOf(vpiElement, By("top.pavar1"));
  ASSERT_EQ(kRows.size(), 2U);
  EXPECT_EQ(vpi_get(vpiPackedArrayMember, kRows[1]), 1);
  const std::vector<vpiHandle> kEnums = ObjectsOf(vpiElement, By("top.e"));
  ASSERT_EQ(kEnums.size(), 3U);
  EXPECT_EQ(vpi_get(vpiPackedArrayMember, kEnums[0]), 1);
  const std::vector<vpiHandle> kUnions = ObjectsOf(vpiElement, By("top.u"));
  ASSERT_EQ(kUnions.size(), 2U);
  EXPECT_EQ(vpi_get(vpiPackedArrayMember, kUnions[0]), 1);
}

TEST_F(PackedArrayVarsOfARun, AStructVarOutsideAPackedArrayVarIsNoMemberOfOne) {
  Run(std::string("module top;\n") + kStructTypedef + "  pst s;\nendmodule\n");
  ASSERT_NE(By("top.s"), nullptr);
  EXPECT_EQ(vpi_get(vpiPackedArrayMember, By("top.s")), 0);
}

TEST_F(PackedArrayVarsOfARun,
       AStructsPackedArrayVarMemberIsNoPackedArrayMember) {
  Run(AggregateMembersDesign());
  vpiHandle member = Named(vpiMember, By("top.us"), "pa");
  ASSERT_NE(member, nullptr);
  EXPECT_EQ(vpi_get(vpiPackedArrayMember, member), 0);
}

TEST_F(PackedArrayVarsOfARun,
       DISABLED_AMembersSubelementsArePackedArrayMembers) {
  Run(AggregateMembersDesign());
  vpiHandle member = Named(vpiMember, By("top.us"), "pa");
  ASSERT_NE(member, nullptr);
  const std::vector<vpiHandle> kElements = ObjectsOf(vpiElement, member);
  ASSERT_EQ(kElements.size(), 4U);
  for (vpiHandle element : kElements) {
    EXPECT_EQ(vpi_get(vpiPackedArrayMember, element), 1);
  }
}

TEST_F(PackedArrayVarsOfARun, APackedArrayVarAndEverySubelementArePacked) {
  Run(ElementKindsDesign());
  vpiHandle pavar1 = By("top.pavar1");
  const std::vector<vpiHandle> kRows = ObjectsOf(vpiElement, pavar1);
  ASSERT_EQ(kRows.size(), 2U);
  const std::vector<vpiHandle> kLeaves = ObjectsOf(vpiElement, kRows[1]);
  ASSERT_EQ(kLeaves.size(), 2U);
  const std::vector<vpiHandle> kEnums = ObjectsOf(vpiElement, By("top.e"));
  ASSERT_EQ(kEnums.size(), 3U);
  const std::vector<vpiHandle> kUnions = ObjectsOf(vpiElement, By("top.u"));
  ASSERT_EQ(kUnions.size(), 2U);
  for (vpiHandle obj : {pavar1, kRows[1], kLeaves[0], By("top.e"), kEnums[0],
                        By("top.u"), kUnions[0]}) {
    EXPECT_EQ(vpi_get(vpiPacked, obj), 1) << vpi_get_str(vpiName, obj);
  }
}

TEST_F(PackedArrayVarsOfARun, AnEnumOrUnionUnderAnInnerRowIsPacked) {
  Run(std::string("module top;\n") + kEnumAndUnionTypedefs +
      "  et [1:0][2:0] e2; ut [0:1][1:0] u2;\n"
      "endmodule\n");
  const std::vector<vpiHandle> kEnumRows = ObjectsOf(vpiElement, By("top.e2"));
  ASSERT_EQ(kEnumRows.size(), 2U);
  const std::vector<vpiHandle> kEnums = ObjectsOf(vpiElement, kEnumRows[1]);
  ASSERT_EQ(kEnums.size(), 3U);
  const std::vector<vpiHandle> kUnionRows = ObjectsOf(vpiElement, By("top.u2"));
  ASSERT_EQ(kUnionRows.size(), 2U);
  const std::vector<vpiHandle> kUnions = ObjectsOf(vpiElement, kUnionRows[1]);
  ASSERT_EQ(kUnions.size(), 2U);
  for (vpiHandle obj : {kEnumRows[1], kEnums[2], kUnionRows[1], kUnions[0]}) {
    EXPECT_EQ(vpi_get(vpiPacked, obj), 1) << vpi_get_str(vpiName, obj);
  }
}

TEST_F(PackedArrayVarsOfARun, AnEnumOrUnionPackedArrayVarIsSizedInBits) {
  Run(std::string("module top;\n") + kEnumAndUnionTypedefs +
      "  et [2:0] e; ut [1:0] u; et [1:0][2:0] e2;\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiSize, By("top.e")), 3 * 2);
  EXPECT_EQ(vpi_get(vpiSize, By("top.u")), 2 * 4);
  vpiHandle e2 = By("top.e2");
  EXPECT_EQ(vpi_get(vpiSize, e2), 6 * 2);
  const std::vector<vpiHandle> kRows = ObjectsOf(vpiElement, e2);
  ASSERT_EQ(kRows.size(), 2U);
  EXPECT_EQ(vpi_get(vpiSize, kRows[0]), 3 * 2);
}

TEST_F(PackedArrayVarsOfARun,
       DISABLED_APackedArrayVarsRangesMultiplyToItsElementCount) {
  Run(std::string("module top;\n") + kStructTypedef +
      "  pst [0:1][2:0] v;\n"
      "endmodule\n");
  vpiHandle v = By("top.v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(vpi_get(vpiSize, v), 6 * 36);
  EXPECT_EQ(RangeSizesOf(v), (std::vector<int>{2, 3}));
  EXPECT_EQ(BoundsOf(v), (std::vector<int>{0, 1, 2, 0}));
}

TEST_F(PackedArrayVarsOfARun, APackedArrayVarAndEverySubelementAreVectors) {
  Run("module top;\n"
      "  typedef struct packed { logic [3:0] a; } s_t;\n"
      "  typedef enum bit { A, B } e_t;\n"
      "  typedef union packed { logic [3:0] a; bit [3:0] b; } ut;\n"
      "  s_t [1:0][2:0] v; e_t [3:0] ev; ut [1:0] u;\n"
      "endmodule\n");
  vpiHandle v = By("top.v");
  const std::vector<vpiHandle> kRows = ObjectsOf(vpiElement, v);
  ASSERT_EQ(kRows.size(), 2U);
  const std::vector<vpiHandle> kLeaves = ObjectsOf(vpiElement, kRows[1]);
  ASSERT_EQ(kLeaves.size(), 3U);
  vpiHandle ev = By("top.ev");
  const std::vector<vpiHandle> kEnums = ObjectsOf(vpiElement, ev);
  ASSERT_EQ(kEnums.size(), 4U);
  vpiHandle u = By("top.u");
  const std::vector<vpiHandle> kUnions = ObjectsOf(vpiElement, u);
  ASSERT_EQ(kUnions.size(), 2U);
  for (vpiHandle obj :
       {v, kRows[1], kLeaves[0], ev, kEnums[0], u, kUnions[0]}) {
    EXPECT_EQ(vpi_get(vpiVector, obj), 1) << vpi_get_str(vpiName, obj);
    EXPECT_EQ(vpi_get(vpiScalar, obj), 0) << vpi_get_str(vpiName, obj);
  }
}

TEST_F(PackedArrayVarsOfARun,
       DISABLED_APackedArrayVarMemberOfAStructOrUnionIsAMember) {
  Run(AggregateMembersDesign());
  for (const char* name : {"top.ps", "top.pu", "top.us", "top.uu"}) {
    vpiHandle member = Named(vpiMember, By(name), "pa");
    ASSERT_NE(member, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiType, member), vpiPackedArrayVar) << name;
    EXPECT_EQ(vpi_get(vpiStructUnionMember, member), 1) << name;
  }
}

TEST_F(PackedArrayVarsOfARun,
       AModulesPackedArrayVarAndItsSubelementsAreNoMembers) {
  Run(AggregateMembersDesign());
  vpiHandle pa = By("top.pa");
  ASSERT_NE(pa, nullptr);
  EXPECT_EQ(vpi_get(vpiType, pa), vpiPackedArrayVar);
  EXPECT_EQ(vpi_get(vpiStructUnionMember, pa), 0);
  const std::vector<vpiHandle> kElements = ObjectsOf(vpiElement, pa);
  ASSERT_EQ(kElements.size(), 4U);
  for (vpiHandle element : kElements) {
    EXPECT_EQ(vpi_get(vpiStructUnionMember, element), 0);
  }
}

TEST_F(PackedArrayVarsOfARun,
       DISABLED_AMembersSubelementsAreNoStructUnionMembers) {
  Run(AggregateMembersDesign());
  vpiHandle member = Named(vpiMember, By("top.us"), "pa");
  ASSERT_NE(member, nullptr);
  const std::vector<vpiHandle> kElements = ObjectsOf(vpiElement, member);
  ASSERT_EQ(kElements.size(), 4U);
  for (vpiHandle element : kElements) {
    EXPECT_EQ(vpi_get(vpiStructUnionMember, element), 0);
  }
}

std::string ThreeDimensionsDesign() {
  return std::string("module top;\n") + kStructTypedef +
         "  pst [1:0][0:2][3:0] v;\n"
         "endmodule\n";
}

TEST_F(PackedArrayVarsOfARun, EverySubelementsParentIsTheOutermostVar) {
  Run(ThreeDimensionsDesign());
  vpiHandle v = By("top.v");
  ASSERT_NE(v, nullptr);
  const std::vector<vpiHandle> kRows = ObjectsOf(vpiElement, v);
  ASSERT_EQ(kRows.size(), 2U);
  const std::vector<vpiHandle> kMiddle = ObjectsOf(vpiElement, kRows[0]);
  ASSERT_EQ(kMiddle.size(), 3U);
  const std::vector<vpiHandle> kLeaves = ObjectsOf(vpiElement, kMiddle[2]);
  ASSERT_EQ(kLeaves.size(), 4U);
  EXPECT_EQ(ParentOf(kRows[0]), VpiObjectOf(v));
  EXPECT_EQ(ParentOf(kMiddle[2]), VpiObjectOf(v));
  EXPECT_EQ(ParentOf(kLeaves[3]), VpiObjectOf(v));
}

TEST_F(PackedArrayVarsOfARun, AnEnumOrUnionSubelementsParentIsTheOutermostVar) {
  Run(ElementKindsDesign());
  const std::vector<vpiHandle> kEnums = ObjectsOf(vpiElement, By("top.e"));
  ASSERT_EQ(kEnums.size(), 3U);
  EXPECT_EQ(ParentOf(kEnums[0]), VpiObjectOf(By("top.e")));
  const std::vector<vpiHandle> kUnions = ObjectsOf(vpiElement, By("top.u"));
  ASSERT_EQ(kUnions.size(), 2U);
  EXPECT_EQ(ParentOf(kUnions[1]), VpiObjectOf(By("top.u")));
}

TEST_F(PackedArrayVarsOfARun, DISABLED_AMembersSubelementsParentIsTheMember) {
  Run(AggregateMembersDesign());
  vpiHandle member = Named(vpiMember, By("top.us"), "pa");
  ASSERT_NE(member, nullptr);
  EXPECT_EQ(ParentOf(member), VpiObjectOf(By("top.us")));
  const std::vector<vpiHandle> kElements = ObjectsOf(vpiElement, member);
  ASSERT_EQ(kElements.size(), 4U);
  EXPECT_EQ(ParentOf(kElements[0]), VpiObjectOf(member));
}

TEST_F(PackedArrayVarsOfARun, AThreeDimensionalVarIsWalkedOneRangeAtATime) {
  Run(ThreeDimensionsDesign());
  vpiHandle v = By("top.v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(ElementNamesOf(v), (std::vector<std::string>{"v[1]", "v[0]"}));
  const std::vector<vpiHandle> kRows = ObjectsOf(vpiElement, v);
  ASSERT_EQ(kRows.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kRows[0]), vpiPackedArrayVar);
  EXPECT_EQ(vpi_get(vpiSize, kRows[0]), 12 * 36);
  EXPECT_EQ(ElementNamesOf(kRows[0]),
            (std::vector<std::string>{"v[1][0]", "v[1][1]", "v[1][2]"}));
  const std::vector<vpiHandle> kMiddle = ObjectsOf(vpiElement, kRows[0]);
  ASSERT_EQ(kMiddle.size(), 3U);
  EXPECT_EQ(vpi_get(vpiType, kMiddle[0]), vpiPackedArrayVar);
  EXPECT_EQ(vpi_get(vpiSize, kMiddle[0]), 4 * 36);
  EXPECT_EQ(ElementNamesOf(kMiddle[0]),
            (std::vector<std::string>{"v[1][0][3]", "v[1][0][2]", "v[1][0][1]",
                                      "v[1][0][0]"}));
  EXPECT_EQ(KindsOf(vpiElement, kMiddle[0]),
            (std::vector<int>{vpiStructVar, vpiStructVar, vpiStructVar,
                              vpiStructVar}));
}

TEST_F(PackedArrayVarsOfARun,
       AMultidimensionalEnumOrUnionVarEndsInItsElements) {
  Run(std::string("module top;\n") + kEnumAndUnionTypedefs +
      "  et [1:0][2:0] e2; ut [0:1][1:0] u2;\n"
      "endmodule\n");
  vpiHandle e2 = By("top.e2");
  ASSERT_NE(e2, nullptr);
  EXPECT_EQ(ElementNamesOf(e2), (std::vector<std::string>{"e2[1]", "e2[0]"}));
  EXPECT_EQ(KindsOf(vpiElement, e2),
            (std::vector<int>{vpiPackedArrayVar, vpiPackedArrayVar}));
  const std::vector<vpiHandle> kEnumRows = ObjectsOf(vpiElement, e2);
  ASSERT_EQ(kEnumRows.size(), 2U);
  EXPECT_EQ(ElementNamesOf(kEnumRows[0]),
            (std::vector<std::string>{"e2[1][2]", "e2[1][1]", "e2[1][0]"}));
  EXPECT_EQ(KindsOf(vpiElement, kEnumRows[0]),
            (std::vector<int>{vpiEnumVar, vpiEnumVar, vpiEnumVar}));
  vpiHandle u2 = By("top.u2");
  ASSERT_NE(u2, nullptr);
  EXPECT_EQ(ElementNamesOf(u2), (std::vector<std::string>{"u2[0]", "u2[1]"}));
  const std::vector<vpiHandle> kUnionRows = ObjectsOf(vpiElement, u2);
  ASSERT_EQ(kUnionRows.size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kUnionRows[0]), vpiPackedArrayVar);
  EXPECT_EQ(ElementNamesOf(kUnionRows[0]),
            (std::vector<std::string>{"u2[0][1]", "u2[0][0]"}));
  EXPECT_EQ(KindsOf(vpiElement, kUnionRows[0]),
            (std::vector<int>{vpiUnionVar, vpiUnionVar}));
}

TEST_F(PackedArrayVarsOfARun, ARowsIndexIsItsOwnAndTheWholeVarHasNone) {
  Run(ThreeDimensionsDesign());
  vpiHandle v = By("top.v");
  ASSERT_NE(v, nullptr);
  const std::vector<vpiHandle> kRows = ObjectsOf(vpiElement, v);
  ASSERT_EQ(kRows.size(), 2U);
  EXPECT_EQ(IntsOf(vpiIndex, kRows[0]), (std::vector<int>{1}));
  EXPECT_EQ(IntsOf(vpiIndex, kRows[1]), (std::vector<int>{0}));
  EXPECT_EQ(vpi_iterate(vpiIndex, v), nullptr);
}

TEST_F(PackedArrayVarsOfARun,
       DISABLED_ADeeperSubelementsIndicesRunFromItsOwnOutward) {
  Run(ThreeDimensionsDesign());
  vpiHandle v = By("top.v");
  ASSERT_NE(v, nullptr);
  const std::vector<vpiHandle> kRows = ObjectsOf(vpiElement, v);
  ASSERT_EQ(kRows.size(), 2U);
  const std::vector<vpiHandle> kMiddle = ObjectsOf(vpiElement, kRows[0]);
  ASSERT_EQ(kMiddle.size(), 3U);
  const std::vector<vpiHandle> kLeaves = ObjectsOf(vpiElement, kMiddle[2]);
  ASSERT_EQ(kLeaves.size(), 4U);
  EXPECT_EQ(IntsOf(vpiIndex, kMiddle[2]), (std::vector<int>{2, 1}));
  EXPECT_EQ(IntsOf(vpiIndex, kLeaves[3]), (std::vector<int>{0, 2, 1}));
}

TEST_F(PackedArrayVarsOfARun, DISABLED_ARowsTypespecIsTheVarsTypeLessOneRange) {
  Run(ElementKindsDesign());
  const std::vector<vpiHandle> kRows = ObjectsOf(vpiElement, By("top.pavar1"));
  ASSERT_EQ(kRows.size(), 2U);
  vpiHandle row = vpi_handle(vpiTypespec, kRows[1]);
  ASSERT_NE(row, nullptr);
  EXPECT_EQ(vpi_get(vpiType, row), vpiPackedArrayTypespec);
  EXPECT_EQ(BoundsOf(row), (std::vector<int>{1, 0}));
  vpiHandle element = vpi_handle(vpiElemTypespec, row);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(vpi_get(vpiType, element), vpiStructTypespec);
  EXPECT_STREQ(vpi_get_str(vpiName, element), "pst");
}

TEST_F(PackedArrayVarsOfARun, DISABLED_ALeafsTypespecIsTheVarsStructType) {
  Run(ElementKindsDesign());
  const std::vector<vpiHandle> kRows = ObjectsOf(vpiElement, By("top.pavar1"));
  ASSERT_EQ(kRows.size(), 2U);
  const std::vector<vpiHandle> kLeaves = ObjectsOf(vpiElement, kRows[1]);
  ASSERT_EQ(kLeaves.size(), 2U);
  vpiHandle leaf = vpi_handle(vpiTypespec, kLeaves[0]);
  ASSERT_NE(leaf, nullptr);
  EXPECT_EQ(vpi_get(vpiType, leaf), vpiStructTypespec);
  EXPECT_STREQ(vpi_get_str(vpiName, leaf), "pst");
}

TEST_F(PackedArrayVarsOfARun,
       DISABLED_ALeafsTypespecIsTheTypeOfTheVarsElements) {
  Run(std::string("package pk;\n"
                  "  typedef struct packed { logic [3:0] a; } ps_t;\n"
                  "endpackage\n"
                  "module top;\n") +
      kEnumAndUnionTypedefs +
      "  et [2:0] e; ut [1:0] u; pk::ps_t [1:0] pv;\n"
      "  struct packed { logic [3:0] a; logic [3:0] b; } [1:0] v;\n"
      "endmodule\n");
  const auto kLeafOf = [](const char* name) {
    const std::vector<vpiHandle> kLeaves = ObjectsOf(vpiElement, By(name));
    return kLeaves.empty() ? nullptr : kLeaves[0];
  };
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiTypespec, kLeafOf("top.e"))),
            vpiEnumTypespec);
  EXPECT_EQ(TypespecNameOf(kLeafOf("top.e")), "et");
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiTypespec, kLeafOf("top.u"))),
            vpiUnionTypespec);
  EXPECT_EQ(TypespecNameOf(kLeafOf("top.u")), "ut");
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiTypespec, kLeafOf("top.pv"))),
            vpiStructTypespec);
  EXPECT_EQ(TypespecNameOf(kLeafOf("top.pv")), "ps_t");
  vpiHandle inline_leaf = vpi_handle(vpiTypespec, kLeafOf("top.v"));
  ASSERT_NE(inline_leaf, nullptr);
  EXPECT_EQ(vpi_get(vpiType, inline_leaf), vpiStructTypespec);
  EXPECT_EQ(NamesOf(vpiTypespecMember, inline_leaf),
            (std::vector<std::string>{"a", "b"}));
}

TEST_F(PackedArrayVarsOfARun, APackedArrayVarsSubelementsAreConstantSelects) {
  Run(ElementKindsDesign());
  vpiHandle pavar1 = By("top.pavar1");
  ASSERT_NE(pavar1, nullptr);
  const std::vector<vpiHandle> kRows = ObjectsOf(vpiElement, pavar1);
  ASSERT_EQ(kRows.size(), 2U);
  const std::vector<vpiHandle> kLeaves = ObjectsOf(vpiElement, kRows[0]);
  ASSERT_EQ(kLeaves.size(), 2U);
  EXPECT_EQ(vpi_get(vpiConstantSelect, pavar1), 1);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kRows[0]), 1);
  EXPECT_EQ(vpi_get(vpiConstantSelect, kLeaves[1]), 1);
}

}  // namespace
}  // namespace delta
