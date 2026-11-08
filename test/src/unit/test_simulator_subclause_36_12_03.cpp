#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiCompatibilityLimits : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

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

  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &string_var);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

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
