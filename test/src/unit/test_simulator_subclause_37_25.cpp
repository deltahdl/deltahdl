#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "helpers_vpi_two_fixed_unpacked_dims.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

TEST(Typespec, TypespecClassMembership) {
  EXPECT_TRUE(VpiIsTypespecType(vpiEnumTypespec));
  EXPECT_TRUE(VpiIsTypespecType(vpiStructTypespec));
  EXPECT_TRUE(VpiIsTypespecType(vpiArrayTypespec));
  EXPECT_TRUE(VpiIsTypespecType(vpiPackedArrayTypespec));
  EXPECT_TRUE(VpiIsTypespecType(vpiTypeParameter));
  EXPECT_FALSE(VpiIsTypespecType(vpiConstant));
  EXPECT_FALSE(VpiIsTypespecType(vpiStructVar));
}

TEST(Typespec, TypespecClassAdmitsEveryFigureNode) {
  const int kFigureNodes[] = {
      vpiLongIntTypespec,   vpiShortIntTypespec, vpiIntTypespec,
      vpiShortRealTypespec, vpiByteTypespec,     vpiClassTypespec,
      vpiStringTypespec,    vpiUnionTypespec,    vpiBitTypespec,
      vpiLogicTypespec,     vpiVoidTypespec,     vpiSequenceTypespec,
      vpiPropertyTypespec,  vpiEventTypespec,    vpiInterfaceTypespec,
  };
  for (int node : kFigureNodes) {
    EXPECT_TRUE(VpiIsTypespecType(node)) << "figure typespec node " << node;
  }
}

TEST(Typespec, NameOfUserDefinedTypedef) {
  EXPECT_STREQ(VpiTypespecName(vpiEnumTypespec, true, "colors", nullptr),
               "colors");
}

TEST(Typespec, NameOfBuiltInTypeIsNull) {
  EXPECT_EQ(VpiTypespecName(vpiIntTypespec, false, nullptr, nullptr), nullptr);
}

TEST(Typespec, NameOfClassTypespecIsClassName) {
  EXPECT_STREQ(VpiTypespecName(vpiClassTypespec, false, nullptr, "my_class"),
               "my_class");
}

TEST(Typespec, NameOfInlineFieldMayBeEmpty) {
  const char* name = VpiTypespecName(vpiStructTypespec, true, "", nullptr);
  ASSERT_NE(name, nullptr);
  EXPECT_STREQ(name, "");
}

TEST(Typespec, TypedefAliasChain) {
  VpiObject primary_colors;
  EXPECT_EQ(VpiTypespecTypedefAlias(true, &primary_colors), &primary_colors);
  EXPECT_EQ(VpiTypespecTypedefAlias(false, nullptr), nullptr);
}

TEST(Typespec, OnlyATypespecReachesATypedefAlias) {
  VpiContext ctx;
  VpiObject aliased;
  aliased.type = vpiLogicTypespec;
  VpiObject typespec;
  typespec.type = vpiLogicTypespec;
  typespec.aliased = &aliased;
  EXPECT_EQ(ctx.Handle(vpiTypedefAlias, &typespec), &aliased);
  VpiObject net;
  net.type = vpiNet;
  net.aliased = &aliased;
  EXPECT_EQ(ctx.Handle(vpiTypedefAlias, &net), nullptr);
}

TEST(Typespec, AliasInheritsUnderlyingType) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject aliased;
  aliased.type = vpiTimeTypespec;
  VpiObject my_time;
  my_time.type = vpiTimeTypespec;

  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&my_time)), vpiTimeTypespec);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&aliased)),
            vpi_get(vpiType, VpiHandleOf(&my_time)));

  SetGlobalVpiContext(nullptr);
}

TEST(Typespec, IndexTypespecOnAssociativeArray) {
  VpiObject key;
  EXPECT_EQ(VpiTypespecIndexTypespec(true, false, &key), &key);
}

TEST(Typespec, IndexTypespecNullForWildcardIndex) {
  VpiObject key;
  EXPECT_EQ(VpiTypespecIndexTypespec(true, true, &key), nullptr);
}

TEST(Typespec, IndexTypespecNullForNonAssociativeTypespec) {
  VpiObject key;
  EXPECT_EQ(VpiTypespecIndexTypespec(false, false, &key), nullptr);
}

TEST(Typespec, StructAndUnionExposeMembers) {
  VpiObject a;
  VpiObject b;
  std::vector<VpiHandle> members = {&a, &b};
  EXPECT_EQ(VpiTypespecMembers(vpiStructTypespec, members).size(), 2u);
  EXPECT_EQ(VpiTypespecMembers(vpiUnionTypespec, members).size(), 2u);
}

TEST(Typespec, NonStructTypespecHasNoMembers) {
  VpiObject a;
  std::vector<VpiHandle> members = {&a};
  EXPECT_TRUE(VpiTypespecMembers(vpiEnumTypespec, members).empty());
}

TEST(Typespec, MemberTypespecIsTheTypespecChild) {
  VpiObject member;
  VpiObject member_type;
  member_type.type = vpiIntTypespec;
  VpiObject default_value;
  default_value.type = vpiConstant;
  member.children = {&default_value, &member_type};

  EXPECT_EQ(VpiTypespecChild(&member), &member_type);
}

TEST(Typespec, MemberNameIsTheMembersOwnName) {
  VpiObject member;
  member.name = "a";
  EXPECT_STREQ(VpiTypespecMemberName(&member), "a");
}

TEST(Typespec, MemberDefaultExprIsTheExprChild) {
  VpiObject member;
  VpiObject member_type;
  member_type.type = vpiIntTypespec;
  VpiObject default_value;
  default_value.type = vpiConstant;
  member.children = {&member_type, &default_value};

  EXPECT_EQ(VpiTypespecMemberDefaultExpr(&member), &default_value);
}

TEST(Typespec, MemberWithoutDefaultHasNoExpr) {
  VpiObject member;
  VpiObject member_type;
  member_type.type = vpiIntTypespec;
  member.children = {&member_type};

  EXPECT_EQ(VpiTypespecMemberDefaultExpr(&member), nullptr);
}

TEST(Typespec, MemberTypespecNullWhenNoTypespecChild) {
  VpiObject member;
  VpiObject default_value;
  default_value.type = vpiConstant;
  member.children = {&default_value};

  EXPECT_EQ(VpiTypespecChild(&member), nullptr);
}

TEST(Typespec, MemberRelationsNullHandleSafe) {
  EXPECT_EQ(VpiTypespecChild(nullptr), nullptr);
  EXPECT_EQ(VpiTypespecMemberName(nullptr), nullptr);
  EXPECT_EQ(VpiTypespecMemberDefaultExpr(nullptr), nullptr);
}

TEST(Typespec, ElemTypespecUnwindsUntilNoRangesRemain) {
  VpiObject after_first_unwind;
  VpiObject base_struct;

  EXPECT_EQ(VpiTypespecElemTypespec(true, &after_first_unwind),
            &after_first_unwind);
  EXPECT_EQ(VpiTypespecElemTypespec(false, &base_struct), nullptr);
}

TEST(Typespec, RangeIterationYieldsOneRangePerDimension) {
  VpiObject l0, r0, l1, r1;
  std::vector<VpiArrayDimension> dims =
      MakeTwoFixedUnpackedDims({&l0, &r0, 4}, {&l1, &r1, 3});

  std::vector<VpiRangeDesc> ranges = VpiTypespecRanges(dims);
  ASSERT_EQ(ranges.size(), 2u);
  EXPECT_EQ(VpiRangeLeftRange(ranges[0]), &l0);
  EXPECT_EQ(VpiRangeRightRange(ranges[1]), &r1);
}

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

TEST(Typespec, LeftAndRightRangeNullForEmptyLeftmostDimension) {
  VpiObject l, r;
  std::vector<VpiArrayDimension> dims(1);
  dims[0].kind = VpiDimensionKind::kDynamic;
  dims[0].left_expr = &l;
  dims[0].right_expr = &r;

  EXPECT_EQ(VpiTypespecLeftRange(dims), nullptr);
  EXPECT_EQ(VpiTypespecRightRange(dims), nullptr);
}

TEST(Typespec, LeftAndRightRangeNullWhenNoDimensions) {
  std::vector<VpiArrayDimension> dims;
  EXPECT_EQ(VpiTypespecLeftRange(dims), nullptr);
  EXPECT_EQ(VpiTypespecRightRange(dims), nullptr);
}

TEST(Typespec, UnresolvedTypeParameterActsAsTypespec) {
  VpiObject type_parameter;
  type_parameter.type = vpiTypeParameter;
  VpiObject resolved;
  resolved.type = vpiIntTypespec;

  EXPECT_EQ(VpiTypespecForTypeParameter(&type_parameter, nullptr),
            &type_parameter);
  EXPECT_EQ(VpiTypespecForTypeParameter(&type_parameter, &resolved), &resolved);
}

TEST(TypespecModel, AnImplicitElementRangeIsNoDeclaredDimension) {
  VpiObject left;
  left.type = vpiConstant;
  VpiArrayDimension implicit;
  implicit.implicit_element_range = true;
  VpiArrayDimension declared;
  declared.kind = VpiDimensionKind::kPacked;
  declared.left_expr = &left;
  declared.size = 4;
  const std::vector<VpiArrayDimension> kDims = {implicit, declared};
  const std::vector<VpiRangeDesc> kRanges = VpiTypespecRanges(kDims);
  ASSERT_EQ(kRanges.size(), 1u);
  EXPECT_EQ(kRanges[0].size, 4);
  EXPECT_EQ(VpiTypespecLeftRange(kDims), &left);
}

TEST(TypespecModel, AttachToleratesAnEnumWithoutConstantsAndAnUnbuiltVariable) {
  VpiContext vpi_ctx;
  SetGlobalVpiContext(&vpi_ctx);
  SimFixture f;
  ModuleItem typedef_item;
  typedef_item.kind = ModuleItemKind::kTypedef;
  typedef_item.name = "e_t";
  typedef_item.typedef_type.kind = DataTypeKind::kEnum;
  ModuleDecl decl;
  decl.name = "m";
  decl.items = {&typedef_item};
  CompilationUnit unit;
  unit.modules = {&decl};
  DataType written;
  written.kind = DataTypeKind::kNamed;
  written.type_name = "e_t";
  RtlirModule mod;
  mod.name = "m";
  mod.decl = &decl;
  mod.variables.resize(1);
  mod.variables.front().name = "unbuilt";
  mod.variables.front().written_type = &written;
  RtlirDesign design;
  design.top_modules = {&mod};
  design.compilation_unit = &unit;
  vpi_ctx.Attach(f.ctx, &design);
  vpiHandle m = vpi_handle_by_name(VpiText("m"), nullptr);
  ASSERT_NE(m, nullptr);
  vpiHandle it = vpi_iterate(vpiTypedef, m);
  ASSERT_NE(it, nullptr);
  vpiHandle typespec = vpi_scan(it);
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiEnumTypespec);
  EXPECT_STREQ(vpi_get_str(vpiName, typespec), "e_t");
  EXPECT_EQ(vpi_iterate(vpiEnumConst, typespec), nullptr);
  EXPECT_EQ(vpi_scan(it), nullptr);
  EXPECT_EQ(vpi_handle_by_name(VpiText("m.unbuilt"), nullptr), nullptr);
  SetGlobalVpiContext(nullptr);
}

class TypespecsOfARun : public VpiDesignRun {
 protected:
  static std::vector<int> RangeSizesOf(vpiHandle typespec) {
    std::vector<int> sizes;
    for (vpiHandle range : ObjectsOf(vpiRange, typespec)) {
      sizes.push_back(vpi_get(vpiSize, range));
    }
    return sizes;
  }

  static int ValueOf(vpiHandle bound) {
    if (bound == nullptr) return -1;
    s_vpi_value value{};
    value.format = vpiIntVal;
    vpi_get_value(bound, &value);
    return value.value.integer;
  }

  static int KindReached(int relation, vpiHandle ref) {
    vpiHandle reached = vpi_handle(relation, ref);
    return reached == nullptr ? 0 : vpi_get(vpiType, reached);
  }

  static std::vector<int> EnumConstValuesOf(vpiHandle typespec) {
    std::vector<int> values;
    for (vpiHandle constant : ObjectsOf(vpiEnumConst, typespec)) {
      values.push_back(ValueOf(constant));
    }
    return values;
  }
};

TEST_F(TypespecsOfARun, ATypedefOfATypedefReachesItThroughTypedefAlias) {
  Run("typedef int word_t;\n"
      "module top; typedef logic [3:0] nib_t; typedef nib_t half_t;\n"
      "  typedef word_t whole_t; endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  vpiHandle nib = Named(vpiTypedef, top, "nib_t");
  vpiHandle half = Named(vpiTypedef, top, "half_t");
  ASSERT_NE(nib, nullptr);
  ASSERT_NE(half, nullptr);
  EXPECT_EQ(vpi_get(vpiType, half), vpiLogicTypespec);
  EXPECT_TRUE(vpi_compare_objects(vpi_handle(vpiTypedefAlias, half), nib));
  EXPECT_EQ(vpi_handle(vpiTypedefAlias, nib), nullptr);
  vpiHandle whole = Named(vpiTypedef, top, "whole_t");
  ASSERT_NE(whole, nullptr);
  EXPECT_EQ(vpi_get(vpiType, whole), vpiIntTypespec);
  vpiHandle word = vpi_handle(vpiTypedefAlias, whole);
  ASSERT_NE(word, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, word), "word_t");
}

TEST_F(TypespecsOfARun, ATypedefOfAnImportedTypedefReachesIt) {
  Run("package pk; typedef logic [3:0] nib_t; typedef int word_t;\n"
      "endpackage\n"
      "package qk; typedef bit flag_t; endpackage\n"
      "module top; import qk::*; import pk::word_t; import pk::nib_t;\n"
      "  typedef nib_t half_t; endmodule\n");
  vpiHandle half = Named(vpiTypedef, By("top"), "half_t");
  ASSERT_NE(half, nullptr);
  EXPECT_EQ(vpi_get(vpiType, half), vpiLogicTypespec);
  EXPECT_TRUE(vpi_compare_objects(vpi_handle(vpiTypedefAlias, half),
                                  Named(vpiTypedef, By("pk"), "nib_t")));
}

TEST_F(TypespecsOfARun, RealtimeEventAndChandleTypedefsAreTypespecs) {
  Run("module top; logic clk;\n"
      "  typedef realtime rt_t; typedef event ev_t; typedef chandle ch_t;\n"
      "  property p(rt_t v); @(posedge clk) 1; endproperty\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(KindsOf(vpiTypedef, top),
            (std::vector<int>{vpiRealTypespec, vpiEventTypespec,
                              vpiChandleTypespec}));
  vpiHandle decl = Named(vpiPropertyDecl, top, "p");
  ASSERT_NE(decl, nullptr);
  vpiHandle v = vpi_handle(vpiTypespec, Named(vpiPropFormalDecl, decl, "v"));
  ASSERT_NE(v, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, v), "rt_t");
}

TEST_F(TypespecsOfARun, ABitOrLogicTypespecRangesAndUnwinds) {
  Run("module top;\n"
      "  typedef bit [3:0] nib_t; typedef nib_t [1:0] byte_t;\n"
      "  typedef logic [7:0] b_t;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle nib = Named(vpiTypedef, top, "nib_t");
  vpiHandle byte_t = Named(vpiTypedef, top, "byte_t");
  vpiHandle b = Named(vpiTypedef, top, "b_t");
  ASSERT_NE(nib, nullptr);
  ASSERT_NE(byte_t, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(vpi_get(vpiType, byte_t), vpiBitTypespec);
  EXPECT_EQ(RangeSizesOf(byte_t), (std::vector<int>{2, 4}));
  EXPECT_EQ(ValueOf(vpi_handle(vpiLeftRange, byte_t)), 1);
  EXPECT_EQ(ValueOf(vpi_handle(vpiRightRange, byte_t)), 0);
  EXPECT_EQ(vpi_handle(vpiTypedefAlias, byte_t), nullptr);
  EXPECT_TRUE(vpi_compare_objects(vpi_handle(vpiElemTypespec, byte_t), nib));
  EXPECT_EQ(vpi_get(vpiVector, nib), 1);
  EXPECT_EQ(vpi_get(vpiScalar, nib), 0);
  vpiHandle bit = vpi_handle(vpiElemTypespec, nib);
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(vpi_get(vpiType, bit), vpiBitTypespec);
  EXPECT_EQ(vpi_get_str(vpiName, bit), nullptr);
  EXPECT_TRUE(RangeSizesOf(bit).empty());
  EXPECT_EQ(vpi_get(vpiVector, bit), 0);
  EXPECT_EQ(vpi_handle(vpiElemTypespec, bit), nullptr);
  EXPECT_EQ(vpi_get(vpiType, b), vpiLogicTypespec);
  EXPECT_EQ(ValueOf(vpi_handle(vpiLeftRange, b)), 7);
  EXPECT_EQ(KindReached(vpiElemTypespec, b), vpiLogicTypespec);
}

TEST_F(TypespecsOfARun, DetailEightsArraysUnwindToTheirTypedefs) {
  Run("module top;\n"
      "  typedef struct packed { int i1; bit bvec; } [1:3] parrtype;\n"
      "  typedef parrtype [2:1] parrtype2;\n"
      "  typedef parrtype2 unparrtype [6:4];\n"
      "  unparrtype arr [3:0];\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle parr = Named(vpiTypedef, top, "parrtype");
  vpiHandle parr2 = Named(vpiTypedef, top, "parrtype2");
  vpiHandle unparr = Named(vpiTypedef, top, "unparrtype");
  ASSERT_NE(parr, nullptr);
  ASSERT_NE(parr2, nullptr);
  ASSERT_NE(unparr, nullptr);
  vpiHandle arr = vpi_handle(vpiTypespec, By("top.arr"));
  ASSERT_NE(arr, nullptr);
  EXPECT_EQ(vpi_get(vpiType, arr), vpiArrayTypespec);
  EXPECT_EQ(vpi_get_str(vpiName, arr), nullptr);
  EXPECT_EQ(RangeSizesOf(arr), (std::vector<int>{4, 3}));
  EXPECT_TRUE(vpi_compare_objects(vpi_handle(vpiElemTypespec, arr), unparr));
  EXPECT_EQ(vpi_get(vpiType, unparr), vpiArrayTypespec);
  EXPECT_EQ(vpi_get(vpiArrayType, unparr), vpiStaticArray);
  EXPECT_EQ(RangeSizesOf(unparr), (std::vector<int>{3}));
  EXPECT_EQ(vpi_get(vpiVector, unparr), 0);
  EXPECT_TRUE(vpi_compare_objects(vpi_handle(vpiElemTypespec, unparr), parr2));
  EXPECT_EQ(vpi_get(vpiType, parr2), vpiPackedArrayTypespec);
  EXPECT_EQ(RangeSizesOf(parr2), (std::vector<int>{2, 3}));
  EXPECT_EQ(vpi_get(vpiVector, parr2), 1);
  EXPECT_TRUE(vpi_compare_objects(vpi_handle(vpiElemTypespec, parr2), parr));
  EXPECT_EQ(vpi_get(vpiType, parr), vpiPackedArrayTypespec);
  vpiHandle element = vpi_handle(vpiElemTypespec, parr);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(vpi_get(vpiType, element), vpiStructTypespec);
  EXPECT_EQ(NamesOf(vpiTypespecMember, element),
            (std::vector<std::string>{"bvec", "i1"}));
  EXPECT_EQ(vpi_handle(vpiElemTypespec, element), nullptr);
}

TEST_F(TypespecsOfARun, AnArraysKindAndIndexTypeAreItsLeftmostDimensions) {
  Run("module top; typedef int my_t;\n"
      "  typedef int aa_t [string]; typedef bit ab_t [my_t];\n"
      "  typedef byte aw_t [*]; typedef int da_t []; typedef int q_t [$];\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle aa = Named(vpiTypedef, top, "aa_t");
  vpiHandle ab = Named(vpiTypedef, top, "ab_t");
  vpiHandle aw = Named(vpiTypedef, top, "aw_t");
  vpiHandle da = Named(vpiTypedef, top, "da_t");
  vpiHandle q = Named(vpiTypedef, top, "q_t");
  ASSERT_NE(aa, nullptr);
  ASSERT_NE(da, nullptr);
  EXPECT_EQ(vpi_get(vpiArrayType, aa), vpiAssocArray);
  EXPECT_EQ(KindReached(vpiIndexTypespec, aa), vpiStringTypespec);
  EXPECT_TRUE(vpi_compare_objects(vpi_handle(vpiIndexTypespec, ab),
                                  Named(vpiTypedef, top, "my_t")));
  EXPECT_EQ(vpi_get(vpiArrayType, aw), vpiAssocArray);
  EXPECT_EQ(vpi_handle(vpiIndexTypespec, aw), nullptr);
  EXPECT_EQ(vpi_get(vpiArrayType, da), vpiDynamicArray);
  EXPECT_EQ(vpi_handle(vpiIndexTypespec, da), nullptr);
  EXPECT_EQ(RangeSizesOf(da), (std::vector<int>{0}));
  EXPECT_EQ(vpi_handle(vpiLeftRange, da), nullptr);
  EXPECT_EQ(vpi_get(vpiArrayType, q), vpiQueueArray);
  EXPECT_EQ(KindReached(vpiElemTypespec, q), vpiIntTypespec);
}

TEST_F(TypespecsOfARun, AnAggregatesMembersReachTheirTypesAndDefaults) {
  Run("module top; typedef bit [3:0] nib_t;\n"
      "  typedef struct packed { logic [3:0] a; nib_t b; } ps_t;\n"
      "  typedef union tagged { int i; bit b; } tu_t;\n"
      "  typedef union soft packed { bit [3:0] x; bit [3:0] y; } su_t;\n"
      "  typedef struct { rand int r; randc bit [1:0] c; int d = 5; } us_t;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle ps = Named(vpiTypedef, top, "ps_t");
  vpiHandle us = Named(vpiTypedef, top, "us_t");
  ASSERT_NE(ps, nullptr);
  ASSERT_NE(us, nullptr);
  EXPECT_EQ(vpi_get(vpiPacked, ps), 1);
  vpiHandle a = vpi_handle(vpiTypespec, Named(vpiTypespecMember, ps, "a"));
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(vpi_get(vpiType, a), vpiLogicTypespec);
  EXPECT_EQ(RangeSizesOf(a), (std::vector<int>{4}));
  EXPECT_TRUE(vpi_compare_objects(
      vpi_handle(vpiTypespec, Named(vpiTypespecMember, ps, "b")),
      Named(vpiTypedef, top, "nib_t")));
  vpiHandle tu = Named(vpiTypedef, top, "tu_t");
  vpiHandle su = Named(vpiTypedef, top, "su_t");
  EXPECT_EQ(vpi_get(vpiTagged, tu), 1);
  EXPECT_EQ(vpi_get(vpiSoft, tu), 0);
  EXPECT_EQ(vpi_get(vpiSoft, su), 1);
  EXPECT_EQ(vpi_get(vpiPacked, su), 1);
  EXPECT_EQ(vpi_get(vpiPacked, us), 0);
  vpiHandle r = Named(vpiTypespecMember, us, "r");
  vpiHandle c = Named(vpiTypespecMember, us, "c");
  vpiHandle d = Named(vpiTypespecMember, us, "d");
  EXPECT_EQ(vpi_get(vpiRandType, r), vpiRand);
  EXPECT_EQ(vpi_get(vpiRandType, c), vpiRandC);
  EXPECT_EQ(vpi_get(vpiRandType, d), vpiNotRand);
  EXPECT_EQ(vpi_handle(vpiExpr, r), nullptr);
  vpiHandle value = vpi_handle(vpiExpr, d);
  ASSERT_NE(value, nullptr);
  EXPECT_EQ(vpi_get(vpiType, value), vpiConstant);
  EXPECT_EQ(ValueOf(value), 5);
  EXPECT_EQ(KindReached(vpiTypespec, d), vpiIntTypespec);
}

TEST_F(TypespecsOfARun, EnumsAliasesAndClassesReachWhatTheyStandFor) {
  Run("package pk; typedef logic [1:0] t; endpackage\n"
      "module top;\n"
      "  typedef enum bit [1:0] {red, yellow, blue} primary_colors;\n"
      "  typedef primary_colors colors; typedef enum {X, Y} plain_e;\n"
      "  typedef enum bit [2:0] {P, Q} ea_t [2];\n"
      "  typedef time my_time; typedef pk::t pt_t;\n"
      "  class C; endclass typedef C c_t;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle primary = Named(vpiTypedef, top, "primary_colors");
  vpiHandle colors = Named(vpiTypedef, top, "colors");
  ASSERT_NE(primary, nullptr);
  ASSERT_NE(colors, nullptr);
  vpiHandle base = vpi_handle(vpiBaseTypespec, primary);
  ASSERT_NE(base, nullptr);
  EXPECT_EQ(vpi_get(vpiType, base), vpiBitTypespec);
  EXPECT_EQ(RangeSizesOf(base), (std::vector<int>{2}));
  EXPECT_EQ(vpi_handle(vpiElemTypespec, primary), nullptr);
  EXPECT_EQ(vpi_get(vpiType, colors), vpiEnumTypespec);
  EXPECT_TRUE(
      vpi_compare_objects(vpi_handle(vpiTypedefAlias, colors), primary));
  EXPECT_EQ(NamesOf(vpiEnumConst, colors),
            (std::vector<std::string>{"blue", "red", "yellow"}));
  EXPECT_TRUE(vpi_compare_objects(vpi_handle(vpiBaseTypespec, colors), base));
  EXPECT_EQ(KindReached(vpiBaseTypespec, Named(vpiTypedef, top, "plain_e")),
            vpiIntTypespec);
  vpiHandle enums = vpi_handle(vpiElemTypespec, Named(vpiTypedef, top, "ea_t"));
  ASSERT_NE(enums, nullptr);
  EXPECT_EQ(vpi_get(vpiType, enums), vpiEnumTypespec);
  EXPECT_EQ(RangeSizesOf(vpi_handle(vpiBaseTypespec, enums)),
            (std::vector<int>{3}));
  vpiHandle my_time = Named(vpiTypedef, top, "my_time");
  ASSERT_NE(my_time, nullptr);
  vpiHandle time = vpi_handle(vpiTypedefAlias, my_time);
  ASSERT_NE(time, nullptr);
  EXPECT_EQ(vpi_get(vpiType, time), vpiTimeTypespec);
  EXPECT_EQ(vpi_get_str(vpiName, time), nullptr);
  EXPECT_EQ(vpi_handle(vpiBaseTypespec, my_time), nullptr);
  EXPECT_TRUE(vpi_compare_objects(
      vpi_handle(vpiTypedefAlias, Named(vpiTypedef, top, "pt_t")),
      Named(vpiTypedef, By("pk"), "t")));
  vpiHandle c = Named(vpiTypedef, top, "c_t");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(vpi_get(vpiType, c), vpiClassTypespec);
  EXPECT_TRUE(vpi_compare_objects(vpi_handle(vpiClassDefn, c),
                                  Named(vpiClassDefn, top, "C")));
}

TEST_F(TypespecsOfARun, AMemberWrittenAsAStructureReachesItsOwnTypespec) {
  Run("module top;\n"
      "  typedef struct { struct packed { bit [1:0] lo; logic hi; } inner;\n"
      "                   int x; } n_t;\n"
      "endmodule\n");
  vpiHandle n = Named(vpiTypedef, By("top"), "n_t");
  ASSERT_NE(n, nullptr);
  vpiHandle inner =
      vpi_handle(vpiTypespec, Named(vpiTypespecMember, n, "inner"));
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(vpi_get(vpiType, inner), vpiStructTypespec);
  EXPECT_EQ(vpi_get(vpiPacked, inner), 1);
  EXPECT_EQ(vpi_get_str(vpiName, inner), nullptr);
  EXPECT_EQ(NamesOf(vpiTypespecMember, inner),
            (std::vector<std::string>{"hi", "lo"}));
  EXPECT_EQ(RangeSizesOf(
                vpi_handle(vpiTypespec, Named(vpiTypespecMember, inner, "lo"))),
            (std::vector<int>{2}));
  EXPECT_EQ(KindReached(vpiTypespec, Named(vpiTypespecMember, n, "x")),
            vpiIntTypespec);
}

TEST_F(TypespecsOfARun, AnEnumWithDimsAfterItsBodyIsAPackedArrayOfIt) {
  Run("module top;\n"
      "  typedef enum bit [1:0] {A, B} [3:0] e_t;\n"
      "endmodule\n");
  vpiHandle e = Named(vpiTypedef, By("top"), "e_t");
  ASSERT_NE(e, nullptr);
  EXPECT_EQ(vpi_get(vpiType, e), vpiPackedArrayTypespec);
  EXPECT_EQ(RangeSizesOf(e), (std::vector<int>{4}));
  vpiHandle element = vpi_handle(vpiElemTypespec, e);
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(vpi_get(vpiType, element), vpiEnumTypespec);
  EXPECT_EQ(RangeSizesOf(vpi_handle(vpiBaseTypespec, element)),
            (std::vector<int>{2}));
}

TEST_F(TypespecsOfARun, ATypedefWithNoTypespecLeavesTheOthersInPlace) {
  Run("module top;\n"
      "  parameter type T = int;\n"
      "  typedef T alias_t; typedef T alias_arr [2];\n"
      "  typedef bit [2:0] tri_t [4];\n"
      "endmodule\n");
  vpiHandle tri = Named(vpiTypedef, By("top"), "tri_t");
  ASSERT_NE(tri, nullptr);
  EXPECT_EQ(vpi_get(vpiType, tri), vpiArrayTypespec);
  EXPECT_EQ(RangeSizesOf(tri), (std::vector<int>{4}));
  EXPECT_EQ(KindReached(vpiElemTypespec, tri), vpiBitTypespec);
}

TEST_F(TypespecsOfARun, AForwardTypedefDrawsNoTypespecOfItsOwn) {
  Run("module top;\n"
      "  typedef class C; typedef T; typedef struct s_t;\n"
      "  class C; endclass\n"
      "  typedef int T; typedef struct packed { bit a; } s_t;\n"
      "  C h;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  EXPECT_EQ(NamesOf(vpiTypedef, top), (std::vector<std::string>{"T", "s_t"}));
  EXPECT_EQ(vpi_get(vpiType, Named(vpiTypedef, top, "T")), vpiIntTypespec);
  EXPECT_EQ(vpi_get(vpiType, Named(vpiTypedef, top, "s_t")), vpiStructTypespec);
  vpiHandle h = By("top.h");
  ASSERT_NE(h, nullptr);
  EXPECT_NE(KindReached(vpiTypespec, h), vpiLogicTypespec);
}

TEST_F(TypespecsOfARun, AnEnumElementOfATypedefReachesItsConstants) {
  Run("module top;\n"
      "  typedef enum bit [2:0] {P, Q} ea_t [2];\n"
      "  typedef enum bit [1:0] {A, B} [3:0] e_t;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  vpiHandle unpacked =
      vpi_handle(vpiElemTypespec, Named(vpiTypedef, top, "ea_t"));
  vpiHandle packed = vpi_handle(vpiElemTypespec, Named(vpiTypedef, top, "e_t"));
  ASSERT_NE(unpacked, nullptr);
  ASSERT_NE(packed, nullptr);
  EXPECT_EQ(NamesOf(vpiEnumConst, unpacked),
            (std::vector<std::string>{"P", "Q"}));
  EXPECT_EQ(NamesOf(vpiEnumConst, packed),
            (std::vector<std::string>{"A", "B"}));
  EXPECT_EQ(vpi_get_str(vpiName, unpacked), nullptr);
  EXPECT_EQ(vpi_get_str(vpiName, packed), nullptr);
}

TEST_F(TypespecsOfARun, ATaggedUnionsVoidMemberReachesAVoidTypespec) {
  Run("module top;\n"
      "  typedef union tagged { void Invalid; int Valid; } vint;\n"
      "endmodule\n");
  vpiHandle vint = Named(vpiTypedef, By("top"), "vint");
  ASSERT_NE(vint, nullptr);
  EXPECT_EQ(KindReached(vpiTypespec, Named(vpiTypespecMember, vint, "Invalid")),
            vpiVoidTypespec);
  EXPECT_EQ(KindReached(vpiTypespec, Named(vpiTypespecMember, vint, "Valid")),
            vpiIntTypespec);
}

TEST_F(TypespecsOfARun, AClassesEnumTypedefReachesItsConstants) {
  Run("class U; typedef enum {X = 4, Y} u_t; endclass\n"
      "module top;\n"
      "  class C;\n"
      "    typedef int i_t; typedef enum {A, B = 5, D} e_t;\n"
      "    class N; typedef enum {P = 2, Q} n_t; endclass\n"
      "  endclass\n"
      "endmodule\n");
  vpiHandle c = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(EnumConstValuesOf(Named(vpiTypedef, c, "e_t")),
            (std::vector<int>{0, 5, 6}));
  vpiHandle n = Named(vpiInternalScope, c, "N");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(EnumConstValuesOf(Named(vpiTypedef, n, "n_t")),
            (std::vector<int>{2, 3}));
  vpiHandle u = Named(vpiClassDefn, nullptr, "U");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(EnumConstValuesOf(Named(vpiTypedef, u, "u_t")),
            (std::vector<int>{4, 5}));
}

TEST_F(TypespecsOfARun, AClassPropertyOfATypeParameterReachesIt) {
  Run("package pk; typedef int t; endpackage\n"
      "module top;\n"
      "  class C #(type S = bit, type T = int);\n"
      "    typedef int i_t; T x; S y; int z; pk::t w; i_t v;\n"
      "  endclass\n"
      "endmodule\n");
  vpiHandle c = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(c, nullptr);
  vpiHandle x = vpi_handle(vpiTypespec, Named(vpiVariables, c, "x"));
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(vpi_get(vpiType, x), vpiTypeParameter);
  EXPECT_STREQ(vpi_get_str(vpiName, x), "T");
  vpiHandle y = vpi_handle(vpiTypespec, Named(vpiVariables, c, "y"));
  ASSERT_NE(y, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, y), "S");
  EXPECT_NE(KindReached(vpiTypespec, Named(vpiVariables, c, "z")),
            vpiTypeParameter);
  EXPECT_NE(KindReached(vpiTypespec, Named(vpiVariables, c, "w")),
            vpiTypeParameter);
  EXPECT_NE(KindReached(vpiTypespec, Named(vpiVariables, c, "v")),
            vpiTypeParameter);
}

TEST_F(TypespecsOfARun, ANestedModulesInstanceDeclaresItsTypedefs) {
  Run("module top;\n"
      "  module inner; typedef bit [3:0] nib_t; endmodule\n"
      "  inner i();\n"
      "endmodule\n");
  vpiHandle nib = Named(vpiTypedef, By("top.i"), "nib_t");
  ASSERT_NE(nib, nullptr);
  EXPECT_EQ(vpi_get(vpiType, nib), vpiBitTypespec);
}

}  // namespace
}  // namespace delta
