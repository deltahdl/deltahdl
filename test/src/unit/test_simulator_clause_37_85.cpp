#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.85 Generates: the object model diagram draws a gen scope array, the gen
// scopes it contains, and the gen var that drives a generate. There is no BNF
// and no syntax in this clause; it owns the VPI data model for generates. The
// claims this pass carries through production code and observes here are:
//   * the gen scope array's -> size property (vpiSize), governed by detail 1:
//     the size is the number of elements (gen scopes) in the array;
//   * the gen scope array's -> access by index, drawn with vpi_handle_by_index()
//     / vpi_handle_by_multi_index(): a gen scope array is a valid index-select
//     reference object whose indices select its gen scope elements;
//   * the gen scope's vpiIndex -> expr edge: an array-member gen scope reaches
//     the index expression that locates it within its gen scope array; and
//   * the gen scope's -> is implicitly declared property (vpiImplicitDecl),
//     governed by detail 2: the implicit scope created for an unnamed generate
//     reports TRUE.
// Every other relation in the diagram (vpiInstance, vpiInternalScope, vpiMemory,
// vpiParameter, vpiTypedef, vpiNetTypedef, the names, and the deprecated
// vpiArray/vpiArrayMember/vpiProtected booleans) is served by generic scope,
// instance, typedef, and property machinery owned by §37.10, §37.12, §37.23, and
// §37.25, so it is not re-tested here. Details 3 and 4 (gen var references and
// parameters within a gen scope are treated as local parameters) describe
// elaboration semantics with no §37.85-specific VPI query, and details 5 and 6
// (the vpiTypedef/vpiNetTypedef iterations) restate the instance rule already
// implemented for §37.10, so neither adds production for this clause.
//
// The fixture installs a context so the public vpi_get, vpi_handle, and
// vpi_handle_by_index entry points run their real dispatch over the test objects.
class Generates : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Property (-> size, int: vpiSize), detail 1: a gen scope array reports the
// number of elements in the array - the gen scopes it holds. The count is taken
// from the array's gen scope element children, so a non-element child is not
// counted and a stale stored width is ignored.
TEST_F(Generates, SizeCountsGenScopeElements) {
  VpiObject elem0;
  elem0.type = vpiGenScope;
  VpiObject elem1;
  elem1.type = vpiGenScope;
  VpiObject not_an_element;  // some other related object hanging off the array
  not_an_element.type = vpiNet;

  VpiObject array;
  array.type = vpiGenScopeArray;
  array.size = 99;  // a stored width must not be reported in place of the count
  array.children = {&elem0, &not_an_element, &elem1};

  EXPECT_EQ(vpi_get(vpiSize, &array), 2);
}

// Property (-> size, int: vpiSize), detail 1, boundary: a gen scope array that
// holds no gen scopes reports a size of zero. The count is still computed from
// the (empty) element children, so a stale stored width is not reported in its
// place even at the zero boundary.
TEST_F(Generates, SizeIsZeroForEmptyGenScopeArray) {
  VpiObject array;
  array.type = vpiGenScopeArray;
  array.size = 7;  // a stale stored width must not surface for an empty array

  EXPECT_EQ(vpi_get(vpiSize, &array), 0);
}

// Edge (-> access by index, vpi_handle_by_index()): a gen scope array is a valid
// index-select reference object, and its indices select its gen scope elements.
// An index that names no element yields a null handle.
TEST_F(Generates, ElementsAccessedByIndex) {
  VpiObject elem0;
  elem0.type = vpiGenScope;
  elem0.index = 0;
  VpiObject elem1;
  elem1.type = vpiGenScope;
  elem1.index = 1;

  VpiObject array;
  array.type = vpiGenScopeArray;
  array.children = {&elem0, &elem1};

  EXPECT_EQ(VpiHandleByIndexC(&array, 0), &elem0);
  EXPECT_EQ(VpiHandleByIndexC(&array, 1), &elem1);
  EXPECT_EQ(VpiHandleByIndexC(&array, 2), nullptr);
}

// Edge (-> access by index, vpi_handle_by_multi_index()): the diagram draws the
// multi-index routine alongside the single-index one, so a gen scope array also
// serves as a valid reference object for a multi-index select. The supplied
// index level selects the matching gen scope element.
TEST_F(Generates, ElementSelectedByMultiIndex) {
  VpiObject elem0;
  elem0.type = vpiGenScope;
  elem0.index = 0;
  VpiObject elem1;
  elem1.type = vpiGenScope;
  elem1.index = 1;

  VpiObject array;
  array.type = vpiGenScopeArray;
  array.children = {&elem0, &elem1};

  int indices[] = {1};
  EXPECT_EQ(VpiHandleByMultiIndexC(&array, 1, indices), &elem1);
}

// Edge (vpiIndex -> expr): an array-member gen scope reaches the index
// expression that locates it within its gen scope array.
TEST_F(Generates, IndexReachesArrayMemberIndexExpression) {
  VpiObject index_expr;
  index_expr.type = vpiConstant;

  VpiObject gen_scope;
  gen_scope.type = vpiGenScope;
  gen_scope.array_member = true;
  gen_scope.index_expr = &index_expr;

  EXPECT_EQ(VpiHandleC(vpiIndex, &gen_scope), &index_expr);
}

// Edge (vpiIndex -> expr), gate: a gen scope that is not an element of a gen
// scope array has no locating index, so vpiIndex reports NULL rather than
// returning some other expression child the generic walk might reach.
TEST_F(Generates, IndexIsNullWhenGenScopeIsNotAnArrayMember) {
  VpiObject stray_expr;
  stray_expr.type = vpiConstant;

  VpiObject gen_scope;
  gen_scope.type = vpiGenScope;
  gen_scope.array_member = false;
  gen_scope.index_expr = &stray_expr;  // present but not a locating index

  EXPECT_EQ(VpiHandleC(vpiIndex, &gen_scope), nullptr);
}

// Property (-> is implicitly declared, bool: vpiImplicitDecl), detail 2: the
// implicit scope created for an unnamed generate reports TRUE, while a gen scope
// that was explicitly named reports FALSE - so the property reflects the scope's
// own flag rather than a fixed value.
TEST_F(Generates, ImplicitlyDeclaredScopeReportsTrue) {
  VpiObject implicit_scope;
  implicit_scope.type = vpiGenScope;
  implicit_scope.implicit_decl = true;
  EXPECT_EQ(vpi_get(vpiImplicitDecl, &implicit_scope), 1);

  VpiObject named_scope;
  named_scope.type = vpiGenScope;
  named_scope.implicit_decl = false;
  EXPECT_EQ(vpi_get(vpiImplicitDecl, &named_scope), 0);
}

}  // namespace
}  // namespace delta
