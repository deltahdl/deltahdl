#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.8 Interface task or function declaration: the VPI object model for an
// "interface tf decl". The diagram's two structural edges - the one-to-many
// transitions to the task and function declarations it groups - are walked by
// the generic object-model machinery (vpi_iterate), and the permissive Detail 1
// (vpi_iterate may yield more than one declaration for a vpiForkJoinAcc modport
// task or function imported from several module instances) carries no rule of
// its own beyond what generic iteration already allows.
//
// The clause's own normative rule is Detail 2, observed below through the
// public vpi_get dispatch:
//   D2 - the access type reported for an interface tf decl is only ever
//        vpiForkJoinAcc or vpiExternAcc; no third value escapes the property.

class InterfaceTfDecl : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// D2: a fork-join access type is one of the two legal values and is reported
// back unchanged.
TEST_F(InterfaceTfDecl, ForkJoinAccessTypeReportedVerbatim) {
  VpiObject tf_decl;
  tf_decl.type = vpiInterfaceTfDecl;
  tf_decl.access_type = vpiForkJoinAcc;

  EXPECT_EQ(vpi_get(vpiAccessType, &tf_decl), vpiForkJoinAcc);
}

// D2: an extern access type is the other legal value and is also reported back
// unchanged.
TEST_F(InterfaceTfDecl, ExternAccessTypeReportedVerbatim) {
  VpiObject tf_decl;
  tf_decl.type = vpiInterfaceTfDecl;
  tf_decl.access_type = vpiExternAcc;

  EXPECT_EQ(vpi_get(vpiAccessType, &tf_decl), vpiExternAcc);
}

// D2: any other stored value is not a legal access type for an interface tf
// decl, so the property collapses to vpiUndefined rather than leaking a third
// value - including the zero/unset default.
TEST_F(InterfaceTfDecl, OutOfDomainAccessTypeCollapsesToUndefined) {
  VpiObject odd;
  odd.type = vpiInterfaceTfDecl;
  odd.access_type = 99;  // neither vpiForkJoinAcc nor vpiExternAcc
  EXPECT_EQ(vpi_get(vpiAccessType, &odd), vpiUndefined);

  VpiObject unset;
  unset.type = vpiInterfaceTfDecl;
  unset.access_type = 0;  // default, still not a legal access type
  EXPECT_EQ(vpi_get(vpiAccessType, &unset), vpiUndefined);
}

// D2 scope guard: the interface-tf-decl clamp is keyed on the object type, so
// the other objects the property is drawn on keep their own rules. §37.41
// draws it on the `task func` enclosure, and a task there reports the access it
// was declared with rather than this clause's two values.
TEST_F(InterfaceTfDecl, ClampIsScopedToInterfaceTfDecl) {
  VpiObject task;
  task.type = vpiTask;
  task.access_type = 99;  // would be clamped if the guard were not type-keyed
  EXPECT_EQ(vpi_get(vpiAccessType, &task), 99);
}

// The property is drawn on the interface tf decl, on §37.34's constraint and on
// §37.41's task func enclosure, and on nothing else. An object the data model
// gives no access type reports none, rather than handing back a number the
// diagrams never gave it.
TEST_F(InterfaceTfDecl, AnObjectDrawnWithNoAccessTypeReportsNone) {
  VpiObject net;
  net.type = kVpiNet;
  net.access_type = 99;
  EXPECT_EQ(vpi_get(vpiAccessType, &net), vpiUndefined);
}

}  // namespace
}  // namespace delta
