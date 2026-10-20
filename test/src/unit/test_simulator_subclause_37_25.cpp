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

// §37.25 Typespec: a typespec object describes a type specification. These
// tests observe the production helpers in vpi.cpp that apply the clause's
// numbered "Details" - what vpiName/vpiTypedefAlias report (detail 1), which
// typespecs carry an index typespec (detail 2) and members (detail 3/4), what a
// member's type and default value are (detail 3/7), how vpiElemTypespec unwinds
// an array (detail 8), and how the figure's range relations route through
// §37.22 (details 9 and 10). The figure attributes with no numbered Detail
// (vpiTagged/vpiSoft/ vpiPacked/vpiVector/vpiArrayType/vpiRandType) belong to
// §37.26 and §37.17.

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

// §37.25 figure: the class-membership rule admits every "... typespec" node the
// figure draws, not just the aggregate kinds. The built-in scalar and integer
// typespecs, the string/class/union kinds, the bit/logic kinds, and the
// void/sequence/property/event/interface kinds are each distinct figure nodes
// that a caller may hand to the classifier, so each must be recognized as a
// typespec. (The Annex M spellings vpiIntegerTypespec, vpiRealTypespec,
// vpiTimeTypespec, and vpiChandleTypespec share numeric values with kinds
// already covered here.)
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

// D1: a typespec whose typedef aliases another typedef hands back a handle to
// the aliased typedef; the aliased typedef, not itself an alias, reports NULL.
// This mirrors the colors -> primary_colors example.
TEST(Typespec, TypedefAliasChain) {
  VpiObject primary_colors;
  EXPECT_EQ(VpiTypespecTypedefAlias(/*is_alias=*/true, &primary_colors),
            &primary_colors);
  EXPECT_EQ(VpiTypespecTypedefAlias(/*is_alias=*/false, nullptr), nullptr);
}

// D1: vpiTypedefAlias is drawn on a typespec alone. A typespec reaches the
// typedef its own aliases, and an object of another kind answers the
// relation with nothing, whatever it holds (#5748).
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

// D6: a type defined as an alias of another type inherits the other type's
// vpiType, so both the alias and the aliased typespec report the same type
// code, observed through the existing vpi_get(vpiType). The alias of a time
// typedef reports vpiTimeTypespec, not a distinct alias type.
TEST(Typespec, AliasInheritsUnderlyingType) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject aliased;  // the predefined "time" typespec
  aliased.type = vpiTimeTypespec;
  VpiObject my_time;               // typedef time my_time;
  my_time.type = vpiTimeTypespec;  // inherits the underlying type

  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&my_time)), vpiTimeTypespec);
  EXPECT_EQ(vpi_get(vpiType, VpiHandleOf(&aliased)),
            vpi_get(vpiType, VpiHandleOf(&my_time)));

  SetGlobalVpiContext(nullptr);
}

// D2: vpiIndexTypespec exists only on an associative-array typespec and gives
// the key type.
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

  EXPECT_EQ(VpiTypespecChild(&member), &member_type);
}

// D4: vpiName of a typespec member is the member's own name, not the name of
// the member's type.
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

  EXPECT_EQ(VpiTypespecChild(&member), nullptr);
}

// D3/D4/D7 error condition: the member relations tolerate a null member handle,
// reporting no type, no name, and no default expr rather than dereferencing it.
TEST(Typespec, MemberRelationsNullHandleSafe) {
  EXPECT_EQ(VpiTypespecChild(nullptr), nullptr);
  EXPECT_EQ(VpiTypespecMemberName(nullptr), nullptr);
  EXPECT_EQ(VpiTypespecMemberDefaultExpr(nullptr), nullptr);
}

// D8: vpiElemTypespec unwinds one dimension at a time. While the typespec still
// has a range it hands back the element typespec (the next unwinding level);
// once no ranges remain it yields NULL. This walks the figure's arr example:
// a 4x3 unpacked array typespec -> ... -> base struct typespec.
TEST(Typespec, ElemTypespecUnwindsUntilNoRangesRemain) {
  VpiObject after_first_unwind;  // 3-element unpacked array typespec
  VpiObject base_struct;         // the non-array element, no ranges left

  // The outer typespec still has unpacked ranges, so unwinding yields the next
  // level.
  EXPECT_EQ(VpiTypespecElemTypespec(/*has_ranges=*/true, &after_first_unwind),
            &after_first_unwind);
  // The base struct typespec has no ranges, so vpiElemTypespec is NULL.
  EXPECT_EQ(VpiTypespecElemTypespec(/*has_ranges=*/false, &base_struct),
            nullptr);
}

// D10: vpi_iterate(vpiRange, array_typespec) returns one range per declared
// dimension, leftmost to rightmost.
TEST(Typespec, RangeIterationYieldsOneRangePerDimension) {
  VpiObject l0, r0, l1, r1;
  std::vector<VpiArrayDimension> dims =
      MakeTwoFixedUnpackedDims({&l0, &r0, 4}, {&l1, &r1, 3});

  std::vector<VpiRangeDesc> ranges = VpiTypespecRanges(dims);
  ASSERT_EQ(ranges.size(), 2u);
  EXPECT_EQ(VpiRangeLeftRange(ranges[0]), &l0);
  EXPECT_EQ(VpiRangeRightRange(ranges[1]), &r1);
}

// D10: a dynamic, associative, or queue dimension of the typespec contributes
// an empty range (§37.22).
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

// D9: vpiLeftRange/vpiRightRange of a typespec report the bounds of the
// leftmost declared dimension (leftmost packed for a logic/bit/packed-array
// typespec, leftmost unpacked for an array typespec).
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

// D9: a typespec with no declared dimension has neither a left nor a right
// range.
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

// §37.25 details 9 and 10: an implicit element range is no declared dimension
// of the typespec, so the ranges and the leftmost range pass over it.
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

// §37.25 with §37.17: attaching a design makes a typespec for each typedef an
// instance's declaration writes. An enumeration the elaborated module records
// no constants for is a typespec with none, and a variable of the typedef that
// the run built no object for is passed over rather than related to it.
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

// A design run with a PLI application registered, its VPI model read back
// once the run is over.
class TypespecsOfARun : public VpiDesignRun {
 protected:
  // The sizes of the ranges `typespec` iterates, leftmost first.
  static std::vector<int> RangeSizesOf(vpiHandle typespec) {
    std::vector<int> sizes;
    for (vpiHandle range : ObjectsOf(vpiRange, typespec)) {
      sizes.push_back(vpi_get(vpiSize, range));
    }
    return sizes;
  }

  // The value of the integer constant `bound`, -1 for none.
  static int ValueOf(vpiHandle bound) {
    if (bound == nullptr) return -1;
    s_vpi_value value{};
    value.format = vpiIntVal;
    vpi_get_value(bound, &value);
    return value.value.integer;
  }

  // The kind of what `relation` reaches from `ref`, 0 for nothing.
  static int KindReached(int relation, vpiHandle ref) {
    vpiHandle reached = vpi_handle(relation, ref);
    return reached == nullptr ? 0 : vpi_get(vpiType, reached);
  }

  // The values of the enum consts `typespec` reaches, in declaration order.
  static std::vector<int> EnumConstValuesOf(vpiHandle typespec) {
    std::vector<int> values;
    for (vpiHandle constant : ObjectsOf(vpiEnumConst, typespec)) {
      values.push_back(ValueOf(constant));
    }
    return values;
  }
};

// Detail 1: a typedef of another typedef is a typespec of the aliased one's
// kind, reaching it through vpiTypedefAlias, whether the typedef it aliases
// is the module's or the compilation unit's; a typedef of a type of its own
// aliases none (#5748).
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

// Detail 1: a module typedef aliasing a typedef a package declares, made
// visible by an import (§26.3), is a typespec of the aliased one's kind that
// reaches the package's typespec, past a wildcard import of a package
// declaring no such typedef and an import of another of the package's
// typedefs (#5751).
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

// §37.25: a typedef of realtime is a real typespec (§6.12), one of event an
// event typespec and one of chandle a chandle typespec, each among the
// module's typedefs; a property formal of the realtime one reaches it
// (#5754).
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

// Details 8 to 10: a bit or logic typespec ranges over its packed dimensions,
// those of a typedef it is written over included, its leftmost one's bounds
// being its vpiLeftRange and vpiRightRange, and is a vector; vpiElemTypespec
// unwinds it a range at a time, to the typedef it is written over and then to
// a bit typespec of no ranges and no name, which is no vector and unwinds to
// nothing (#7094, #7095, #7096).
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

// Detail 8's example: a packed array typespec of packed structs, one over it
// ranging over both, an array typespec over that, and a variable's own
// unpacked dimensions over the last making an unnamed array typespec of both
// unpacked ones, each unwinding to the typedef it is written over and the
// structure to nothing (#7083, #7084, #7096, #7099, #7310).
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

// Details 2, 9 and 10 with §7.5 to §7.10: an array typespec's vpiArrayType is
// the kind of array its leftmost dimension makes, a dynamic, queue or
// associative one being an empty range with no bounds; an associative one's
// vpiIndexTypespec is its index type's typespec, a keyword's or a typedef's,
// and none for the wildcard index or any other array (#7084, #7097).
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

// Details 3, 4 and 7 with §7.2 and §37.26: a struct or union typespec says
// whether it is packed, tagged or soft, and each typespec member reaches the
// typespec of its type, a typedef's where it names one, the default value it
// was declared with through vpiExpr, and says through vpiRandType whether it
// is rand or randc (#7090, #7091, #7092, #7093).
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

// Details 1 and 6 with §6.19 and §37.32: an enum typespec reaches its base
// type's typespec, int's where it names none, through vpiBaseTypespec, which
// no other typespec reaches; a typedef of an enum typedef is an enum typespec
// with its constants and base; one of a predefined type aliases that type's
// unnamed typespec; one of a package's type aliases the package's typedef;
// and one of a class is a class typespec of its own name reaching the class
// defn (#7082, #7088, #7089, #7098).
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

// Detail 5: a member whose type is a structure written in place reaches an
// unnamed typespec of that structure, packed as it was declared, whose own
// members reach their types in turn.
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

// §37.25 detail 8 with §7.4.1: a typedef of an enumeration written with
// packed dimensions after its body is a packed array typespec ranging over
// them, whose element is an enum typespec over the base type the enumeration
// was written with (#7312).
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

// A typedef of a type the run draws no typespec for, a type parameter's,
// written plain or with unpacked dimensions of its own, hangs nothing from its
// scope, and the typedefs declared after it still reach theirs.
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

// §6.18 with detail 1: a forward typedef, of a class, of a structure or bare,
// draws no typespec of its own; the scope's typedefs are those that define
// the types, and a variable of the class is related to no logic typespec named
// after it (#7311).
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

// Detail 8: the enum typespec a typedef's dimensions unwind to is unnamed and
// reaches the constants the typedef's enumeration declares, whether the
// dimensions are unpacked or packed ones written after its body (#7314).
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

// The figure with detail 3 and §7.3.2: a tagged union's void member reaches a
// void typespec, and its other members the typespecs of their own types
// (#7085).
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

// §37.31 with the figure: an enum typedef a class declares reaches its enum
// consts with their values, whether the class is a module's, nested in
// another (§8.23) or the compilation unit's, beside a typedef of another type
// (#7343).
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

// Detail 11 with §37.31: in a class defn, where its type parameters stay
// unresolved, a property declared with one reaches the type parameter itself
// as its typespec, and one declared with any other type does not (#7100).
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

}  // namespace
}  // namespace delta
