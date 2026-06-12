#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.6 Interface: the VPI object model for an interface. The diagram's property
// and structural edges - the global and default clocking blocks
// (vpiGlobalClocking, vpiDefaultClocking), the default disable iff
// expr/distribution (vpiDefaultDisableIff), the instance array the interface
// belongs to, and the one-to-many vpiInstance edges to the interface's interface
// tf decls, modports, mod paths, cont assigns, clocking blocks, nested
// interfaces, interface arrays, and processes - are walked by the generic
// object-model machinery (vpi_handle / vpi_iterate) and carry no rule of their
// own here.
//
// The single numbered Detail carries this clause's own normative rule, observed
// below through the public vpi_handle dispatch:
//   D1 - vpiIndex from an interface reaches the index expression that locates it
//        within an instance array, or NULL when the interface is not an element
//        of an instance array.

// The fixture installs a context so the public VpiHandleC entry point runs its
// real Handle dispatch.
class Interface : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// D1: vpiIndex from an interface that is an element of an instance array reaches
// the index expression that locates it within the array.
TEST_F(Interface, IndexTransitionReachesArrayIndex) {
  VpiObject index_expr;
  index_expr.type = vpiConstant;

  VpiObject member;
  member.type = vpiInterface;
  member.array_member = true;
  member.index_expr = &index_expr;

  EXPECT_EQ(VpiHandleC(vpiIndex, &member), &index_expr);
}

// D1: for an interface that is not part of an instance array, the vpiIndex
// transition returns NULL - even when an expr is hanging off the object, the
// transition is meaningful only for an array element.
TEST_F(Interface, IndexTransitionIsNullWhenNotAnArrayElement) {
  VpiObject stray_expr;
  stray_expr.type = vpiConstant;

  VpiObject standalone;
  standalone.type = vpiInterface;
  standalone.array_member = false;
  standalone.index_expr = &stray_expr;  // present but must not be reported
  standalone.children.push_back(&stray_expr);

  EXPECT_EQ(VpiHandleC(vpiIndex, &standalone), nullptr);
}

// D1 edge: an interface marked as an array element but carrying no recorded
// index expression reports NULL directly. The array-member branch hands back
// whatever index_expr holds - here, none - rather than diverting to the generic
// child walk and surfacing some unrelated expr child.
TEST_F(Interface, IndexTransitionIsNullForArrayElementWithoutIndexExpr) {
  VpiObject child_expr;
  child_expr.type = vpiConstant;

  VpiObject member;
  member.type = vpiInterface;
  member.array_member = true;
  member.index_expr = nullptr;          // array element, but no index recorded
  member.children.push_back(&child_expr);  // must not be reported via vpiIndex

  EXPECT_EQ(VpiHandleC(vpiIndex, &member), nullptr);
}

}  // namespace
}  // namespace delta
