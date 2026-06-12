#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.9 Program: the VPI object model for a program block. The diagram's
// property and structural edges - the default clocking block (vpiDefaultClocking),
// the default disable iff expr/distribution (vpiDefaultDisableIff), the instance
// array the program belongs to, and the one-to-many vpiInstance edges to the
// program's cont assigns, clocking blocks, interfaces, interface arrays, and
// processes - are walked by the generic object-model machinery (vpi_handle /
// vpi_iterate) and carry no rule of their own here.
//
// The single numbered Detail carries this clause's own normative rule, observed
// below through the public vpi_handle dispatch:
//   D1 - vpiIndex from a program reaches the index expression that locates it
//        within an instance array, or NULL when the program is not an element
//        of an instance array.

// The fixture installs a context so the public VpiHandleC entry point runs its
// real Handle dispatch.
class Program : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// D1: vpiIndex from a program that is an element of an instance array reaches
// the index expression that locates it within the array.
TEST_F(Program, IndexTransitionReachesArrayIndex) {
  VpiObject index_expr;
  index_expr.type = vpiConstant;

  VpiObject member;
  member.type = vpiProgram;
  member.array_member = true;
  member.index_expr = &index_expr;

  EXPECT_EQ(VpiHandleC(vpiIndex, &member), &index_expr);
}

// D1: for a program that is not part of an instance array, the vpiIndex
// transition returns NULL - even when an expr is hanging off the object, the
// transition is meaningful only for an array element.
TEST_F(Program, IndexTransitionIsNullWhenNotAnArrayElement) {
  VpiObject stray_expr;
  stray_expr.type = vpiConstant;

  VpiObject standalone;
  standalone.type = vpiProgram;
  standalone.array_member = false;
  standalone.index_expr = &stray_expr;  // present but must not be reported
  standalone.children.push_back(&stray_expr);

  EXPECT_EQ(VpiHandleC(vpiIndex, &standalone), nullptr);
}

}  // namespace
}  // namespace delta
