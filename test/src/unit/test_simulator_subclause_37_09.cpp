#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.9 Program: the VPI object model for a program block. The diagram's
// property and structural edges - the default clocking block
// (vpiDefaultClocking), the default disable iff expr/distribution
// (vpiDefaultDisableIff), the instance array the program belongs to, and the
// one-to-many vpiInstance edges to the program's cont assigns, clocking blocks,
// interfaces, interface arrays, and processes - are walked by the generic
// object-model machinery (vpi_handle / vpi_iterate) and carry no rule of their
// own here.
//
// The single numbered Detail carries this clause's own normative rule, observed
// below through the public vpi_handle dispatch:
//   D1 - vpiIndex from a program reaches the index expression that locates it
//        within an instance array, or NULL when the program is not an element
//        of an instance array.

// The fixture installs a context so the public vpi_handle entry point runs its
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

  EXPECT_EQ(vpi_handle(vpiIndex, &member), &index_expr);
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

  EXPECT_EQ(vpi_handle(vpiIndex, &standalone), nullptr);
}

// -----------------------------------------------------------------------------
// The program's edge to its procedures. §37.9 draws it to `process`, which
// §37.63 draws as a class definition - bold italic letters in a dotted
// enclosure - holding the initial, final and always object definitions. §37.4.1
// makes such an enclosure a grouping rather than an object, so vpiProcess is
// the group's name; matching it against an object's own type, which is what the
// generic traversal does, reached no procedure of any program or module.
// -----------------------------------------------------------------------------

// Class membership: the kinds the enclosure holds are the initial, the final
// and the always procedure. The class constant itself is not one of them, and
// §37.63 detail 1's specialized always forms are vpiAlwaysType values rather
// than kinds beside them.
TEST_F(Program, TheProcessClassGroupsTheThreeProcedureKinds) {
  EXPECT_TRUE(VpiIsProcessType(vpiInitial));
  EXPECT_TRUE(VpiIsProcessType(vpiFinal));
  EXPECT_TRUE(VpiIsProcessType(vpiAlways));

  EXPECT_FALSE(VpiIsProcessType(vpiProcess));
  EXPECT_FALSE(VpiIsProcessType(vpiContAssign));
}

// §37.9 (figure, program ==> process): a program's procedures are what the edge
// drawn to the class reaches, so the iteration hands back the initial, the
// final and the always block the program declares. A continuous assignment,
// which the diagram reaches by an edge of its own, is not one of them.
TEST_F(Program, AProgramIteratesTheProceduresItDeclares) {
  VpiObject initial;
  initial.type = vpiInitial;
  VpiObject assign;
  assign.type = vpiContAssign;
  VpiObject always;
  always.type = vpiAlways;
  VpiObject final_proc;
  final_proc.type = vpiFinal;

  VpiObject program;
  program.type = vpiProgram;
  program.children = {&initial, &assign, &always, &final_proc};

  vpiHandle it = vpi_iterate(vpiProcess, &program);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(vpi_scan(it), &initial);
  EXPECT_EQ(vpi_scan(it), &always);
  EXPECT_EQ(vpi_scan(it), &final_proc);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

// §37.63 detail 1: an always procedure is one object kind whatever form it was
// written in, its form read off vpiAlwaysType. All four forms are reached by
// the one edge, and each still reports the form it was written as.
TEST_F(Program, EveryAlwaysFormIsReachedByTheOneEdge) {
  VpiObject comb;
  comb.type = vpiAlways;
  comb.always_type = vpiAlwaysComb;
  VpiObject latch;
  latch.type = vpiAlways;
  latch.always_type = vpiAlwaysLatch;

  VpiObject program;
  program.type = vpiProgram;
  program.children = {&comb, &latch};

  vpiHandle it = vpi_iterate(vpiProcess, &program);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(vpi_scan(it), &comb);
  EXPECT_EQ(vpi_scan(it), &latch);
  EXPECT_EQ(vpi_scan(it), nullptr);

  EXPECT_EQ(vpi_get(vpiAlwaysType, &comb), vpiAlwaysComb);
  EXPECT_EQ(vpi_get(vpiAlwaysType, &latch), vpiAlwaysLatch);
}

// §37.9 (figure): a program that declares no procedure reaches none, which
// §38.23 reports as no iterator rather than an empty one.
TEST_F(Program, AProgramOfNoProceduresIteratesToNone) {
  VpiObject assign;
  assign.type = vpiContAssign;

  VpiObject program;
  program.type = vpiProgram;
  program.children = {&assign};

  EXPECT_EQ(vpi_iterate(vpiProcess, &program), nullptr);
}

}  // namespace
}  // namespace delta
