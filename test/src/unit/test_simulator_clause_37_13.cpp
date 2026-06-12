#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.13 IO declaration: the VPI object model for an io decl (vpiIODecl), a
// module/UDP/task/function port or argument declaration. These tests observe
// the production helpers in vpi.cpp (and the VpiContext::Handle path they feed)
// that apply the clause's four numbered "Details".
//
// The diagram's properties (vpiName/vpiScalar/vpiSigned/vpiSize/vpiVector) and
// the structural reach from instance/UDP/task-func/module are served by the
// generic Get/Handle machinery and carry no §37.13-specific rule of their own.
// The four details that do - the vpiRef direction for by-ref (detail 1), the
// vpiExpr target kind (detail 2), the undefined direction for an interface/
// modport/virtual-interface io decl (detail 3), and the typespec-equal range
// relations (detail 4) - are exercised below.

// D2: the object kinds the vpiExpr relation of an io decl may draw to - the
// named ref obj / interface tf decl / virtual interface var targets and the
// nets and variables groupings. An unrelated kind is not an expr target.
TEST(IoDeclModel, ExprTargetTypeClassification) {
  EXPECT_TRUE(VpiIsIoDeclExprType(vpiRefObj));
  EXPECT_TRUE(VpiIsIoDeclExprType(vpiInterfaceTfDecl));
  EXPECT_TRUE(VpiIsIoDeclExprType(vpiVirtualInterfaceVar));
  EXPECT_TRUE(VpiIsIoDeclExprType(kVpiNet));
  EXPECT_TRUE(VpiIsIoDeclExprType(kVpiReg));  // a logic var

  EXPECT_FALSE(VpiIsIoDeclExprType(vpiModule));
  EXPECT_FALSE(VpiIsIoDeclExprType(vpiExpr));
}

// D2: a by-reference io decl, or one that is an interface or a modport, has a
// ref obj for its vpiExpr; a virtual-interface io decl has a virtual interface
// var; any other io decl keeps its directly connected expression kind.
TEST(IoDeclModel, ExprTargetKindFollowsPassingMode) {
  // Passed by reference -> ref obj.
  EXPECT_EQ(VpiIoDeclExprType(/*passed_by_reference=*/true,
                              /*is_interface_or_modport=*/false,
                              /*is_virtual_interface=*/false,
                              /*default_expr_type=*/kVpiNet),
            vpiRefObj);
  // An interface or modport io decl -> ref obj, even when not by reference.
  EXPECT_EQ(VpiIoDeclExprType(false, /*is_interface_or_modport=*/true, false,
                              kVpiNet),
            vpiRefObj);
  // A virtual interface io decl -> virtual interface var; this wins over the
  // by-reference/interface routing.
  EXPECT_EQ(VpiIoDeclExprType(true, true, /*is_virtual_interface=*/true,
                              kVpiNet),
            vpiVirtualInterfaceVar);
  // An ordinary input port keeps its connected kind (here a net).
  EXPECT_EQ(VpiIoDeclExprType(false, false, false, /*default=*/kVpiNet),
            kVpiNet);
}

// D2: traversing vpiExpr through the public handle path returns the io decl's
// designated connection child, whose own type is an expr-target kind rather
// than vpiExpr.
TEST(IoDeclPublic, HandleExprReturnsConnectionChild) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject io_decl;
  io_decl.type = vpiIODecl;
  VpiObject ref_obj;
  ref_obj.type = vpiRefObj;
  // A typespec child precedes the connection but is not an expr target, so the
  // traversal must skip past it to the ref obj.
  VpiObject typespec;
  typespec.type = vpiTypespec;
  io_decl.children.push_back(&typespec);
  io_decl.children.push_back(&ref_obj);

  VpiHandle expr = ctx.Handle(vpiExpr, &io_decl);
  ASSERT_EQ(expr, &ref_obj);
  EXPECT_EQ(ctx.Get(vpiType, expr), vpiRefObj);

  // An io decl with no expr-target child yields null.
  VpiObject bare;
  bare.type = vpiIODecl;
  bare.children.push_back(&typespec);
  EXPECT_EQ(ctx.Handle(vpiExpr, &bare), nullptr);

  SetGlobalVpiContext(nullptr);
}

// D1: a port or argument passed by reference reports vpiRef as its direction;
// any other passing mode keeps its declared direction.
TEST(IoDeclModel, ByReferenceReportsVpiRefDirection) {
  EXPECT_EQ(VpiIoDeclDirection(/*declared_direction=*/vpiInput,
                               /*passed_by_reference=*/true,
                               /*expr_is_ref_obj_to_interface_or_modport=*/false,
                               /*expr_is_virtual_interface_var=*/false),
            vpiRef);
  // A plain input keeps its declared direction.
  EXPECT_EQ(VpiIoDeclDirection(vpiInput, false, false, false), vpiInput);
  EXPECT_EQ(VpiIoDeclDirection(vpiOutput, false, false, false), vpiOutput);
  EXPECT_EQ(VpiIoDeclDirection(vpiInout, false, false, false), vpiInout);
}

// D3: the direction is undefined (vpiNoDirection) when vpiExpr is a ref obj
// whose vpiActual is an interface or modport declaration, or when vpiExpr is a
// virtual interface var. Detail 3 wins over the detail-1 by-reference routing.
TEST(IoDeclModel, InterfaceModportAndVirtualInterfaceHaveNoDirection) {
  EXPECT_EQ(VpiIoDeclDirection(vpiInput, /*passed_by_reference=*/true,
                               /*expr_is_ref_obj_to_interface_or_modport=*/true,
                               /*expr_is_virtual_interface_var=*/false),
            vpiNoDirection);
  EXPECT_EQ(VpiIoDeclDirection(vpiInput, /*passed_by_reference=*/false,
                               /*expr_is_ref_obj_to_interface_or_modport=*/false,
                               /*expr_is_virtual_interface_var=*/true),
            vpiNoDirection);
}

// D4: the io decl's range relations are the same as for its corresponding
// typespec (§37.25): one range per declared dimension, leftmost to rightmost,
// with a dynamic/queue/associative dimension contributing an empty range.
TEST(IoDeclModel, RangesMatchCorrespondingTypespec) {
  VpiObject l0, r0, l1, r1;
  std::vector<VpiArrayDimension> dims(2);
  dims[0].kind = VpiDimensionKind::kPacked;
  dims[0].left_expr = &l0;
  dims[0].right_expr = &r0;
  dims[0].size = 8;
  dims[1].kind = VpiDimensionKind::kAssoc;  // becomes an empty range
  dims[1].left_expr = &l1;
  dims[1].right_expr = &r1;
  dims[1].size = 0;

  std::vector<VpiRangeDesc> io_ranges = VpiIoDeclRanges(dims);
  std::vector<VpiRangeDesc> ts_ranges = VpiTypespecRanges(dims);
  ASSERT_EQ(io_ranges.size(), ts_ranges.size());
  for (size_t i = 0; i < io_ranges.size(); ++i) {
    EXPECT_EQ(io_ranges[i].empty, ts_ranges[i].empty);
    EXPECT_EQ(io_ranges[i].left_expr, ts_ranges[i].left_expr);
    EXPECT_EQ(io_ranges[i].right_expr, ts_ranges[i].right_expr);
    EXPECT_EQ(io_ranges[i].size, ts_ranges[i].size);
  }
  // The leftmost dimension is the real packed one, so its bounds surface.
  EXPECT_EQ(io_ranges[0].left_expr, &l0);
  EXPECT_TRUE(io_ranges[1].empty);
}

// D4: vpiLeftRange/vpiRightRange of an io decl are identical to the typespec's,
// including the NULL both relations yield for an empty leftmost range.
TEST(IoDeclModel, LeftRightRangeMatchTypespec) {
  VpiObject l0, r0;
  std::vector<VpiArrayDimension> packed(1);
  packed[0].kind = VpiDimensionKind::kPacked;
  packed[0].left_expr = &l0;
  packed[0].right_expr = &r0;
  packed[0].size = 4;
  EXPECT_EQ(VpiIoDeclLeftRange(packed), VpiTypespecLeftRange(packed));
  EXPECT_EQ(VpiIoDeclRightRange(packed), VpiTypespecRightRange(packed));
  EXPECT_EQ(VpiIoDeclLeftRange(packed), &l0);
  EXPECT_EQ(VpiIoDeclRightRange(packed), &r0);

  // A dynamic leftmost dimension is an empty range, so both relations are NULL,
  // exactly as for the corresponding typespec.
  std::vector<VpiArrayDimension> dynamic(1);
  dynamic[0].kind = VpiDimensionKind::kDynamic;
  EXPECT_EQ(VpiIoDeclLeftRange(dynamic), nullptr);
  EXPECT_EQ(VpiIoDeclRightRange(dynamic), VpiTypespecRightRange(dynamic));
}

// D2 (guard/error): the vpiExpr traversal applies only to an io decl. A null
// handle, or an object of any other kind, has no io decl vpiExpr target and so
// yields null rather than diverting some unrelated object's first child.
TEST(IoDeclModel, ExprTraversalAppliesOnlyToIoDecl) {
  EXPECT_EQ(VpiIoDeclExpr(nullptr), nullptr);

  // A non-io-decl object that happens to carry a ref obj child is not subject to
  // the io decl rule, so its vpiExpr target is not taken.
  VpiObject not_io_decl;
  not_io_decl.type = vpiModule;
  VpiObject ref_obj;
  ref_obj.type = vpiRefObj;
  not_io_decl.children.push_back(&ref_obj);
  EXPECT_EQ(VpiIoDeclExpr(&not_io_decl), nullptr);
}

// D4 (edge): a scalar io decl has no declared dimension, so its corresponding
// typespec has none either - the range iteration is empty and both bound
// relations are NULL, matching the typespec exactly.
TEST(IoDeclModel, ScalarIoDeclHasNoRanges) {
  std::vector<VpiArrayDimension> none;
  EXPECT_TRUE(VpiIoDeclRanges(none).empty());
  EXPECT_EQ(VpiIoDeclRanges(none).size(), VpiTypespecRanges(none).size());
  EXPECT_EQ(VpiIoDeclLeftRange(none), nullptr);
  EXPECT_EQ(VpiIoDeclRightRange(none), nullptr);
  EXPECT_EQ(VpiIoDeclLeftRange(none), VpiTypespecLeftRange(none));
  EXPECT_EQ(VpiIoDeclRightRange(none), VpiTypespecRightRange(none));
}

}  // namespace
}  // namespace delta
