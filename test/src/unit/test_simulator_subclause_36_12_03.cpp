#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §36.12.3 (Limitations of VPI compatibility mechanisms): whoever uses or
// supplies an application under a compatibility mode is advised to check that
// the design, or the part of it the application works on, fits the mode and
// holds no construct only another mode supports. A design that holds one leaves
// the VPI's behavior undefined, and how far an implementation checks constructs
// against the mode is up to it.
//
// The discretion is exercised rather than declined. An application running
// under one of the IEEE 1364 modes that reaches a construct those standards
// have no notion of is told so through §38.2's error, instead of being left
// with a behavior nobody defined - and what it reached still comes back,
// §36.12.2 ruling out the emulation of an older behavior for a newer construct
// that never had one.
//
// Which constructs those are is the annexes' own division: Annex K reserves the
// object-type values 1 through 299 for vpi_user.h and Annex M reserves 600
// through 999 for the SystemVerilog extensions.
class VpiCompatibilityLimits : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// §36.12.3: a design partition consistent with the mode raises nothing. The
// scope holds a variable IEEE 1364 has, so an application in that mode is
// applied to a design it covers.
TEST_F(VpiCompatibilityLimits, AConsistentDesignRaisesNothing) {
  VpiObject integer_var;
  integer_var.type = vpiIntegerVar;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&integer_var};

  ASSERT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1364v2001));

  ASSERT_NE(vpi_iterate(vpiVariables, VpiHandleOf(&scope)), nullptr);
  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

// §36.12.3: a partition that is not consistent with the mode is reported. A
// string variable is a SystemVerilog construct, so an IEEE 1364 application
// reaching one is applied to a design the mechanism does not cover.
TEST_F(VpiCompatibilityLimits, AnInconsistentConstructIsReported) {
  VpiObject string_var;
  string_var.type = vpiStringVar;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&string_var};

  ASSERT_TRUE(vpi_ctx_.SetDefaultCompatibilityMode(vpiMode1364v2001));

  vpiHandle it = vpi_iterate(vpiVariables, VpiHandleOf(&scope));
  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);

  // §36.12.2: the mechanism does not emulate an older behavior for a construct
  // that has none, so the object the application reached is still handed back.
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &string_var);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

// §36.12.3: the checking is of a mode against the design. A run that selected
// no compatibility mode is running the current standard, in which the same
// construct is supported and nothing is reported.
TEST_F(VpiCompatibilityLimits, TheCurrentStandardReportsNothing) {
  VpiObject string_var;
  string_var.type = vpiStringVar;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&string_var};

  ASSERT_NE(vpi_iterate(vpiVariables, VpiHandleOf(&scope)), nullptr);
  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

}  // namespace
}  // namespace delta
