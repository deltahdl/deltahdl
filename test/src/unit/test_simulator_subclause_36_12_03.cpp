#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §36.12.3 (Limitations of VPI compatibility mechanisms): "When a VPI
// application uses the compatibility mode mechanism, the application user and
// application provider should verify that the design or design partition to
// which the application is applied is consistent with the mode, and does not
// include constructs that are only supported in other modes. If the design
// contains unsupported constructs, the behavior of the VPI implementation is
// undefined. The extent of checking for consistency between constructs and mode
// is left to the discretion of the VPI implementation."
//
// The discretion is exercised rather than declined. An application running
// under one of the IEEE 1364 modes that reaches a construct those standards
// have no notion of is told so through §38.2's error, instead of being left
// with a behavior nobody defined - and what it reached still comes back,
// §36.12.2 ruling out emulation of "older behaviors for newer design
// constructs" that have none.
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

  ASSERT_NE(vpi_iterate(vpiVariables, &scope), nullptr);
  SVpiErrorInfo info = {};
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

  vpiHandle it = vpi_iterate(vpiVariables, &scope);
  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);

  // §36.12.2: the mechanism does not emulate an older behavior for a construct
  // that has none, so the object the application reached is still handed back.
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(vpi_scan(it), &string_var);
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

  ASSERT_NE(vpi_iterate(vpiVariables, &scope), nullptr);
  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

}  // namespace
}  // namespace delta
