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
// The clause's own normative rule is Detail 2, observed below through the public
// vpi_get dispatch:
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

// D2 scope guard: the interface-tf-decl clamp is keyed on the object type, so a
// non-interface-tf-decl object is untouched by this clause's rule and passes
// its stored value straight through.
TEST_F(InterfaceTfDecl, ClampIsScopedToInterfaceTfDecl) {
  VpiObject other;
  other.type = vpiReg;
  other.access_type = 99;  // would be clamped if the guard were not type-keyed
  EXPECT_EQ(vpi_get(vpiAccessType, &other), 99);
}

}  // namespace
}  // namespace delta
