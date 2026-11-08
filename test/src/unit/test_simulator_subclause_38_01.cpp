#include <gtest/gtest.h>

#include "helpers_vpi_error_fixture.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

using VpiArgumentConventions = VpiErrorRaisingFixture;

TEST_F(VpiArgumentConventions, AnOmittedMandatoryArgumentMakesTheCallFail) {
  EXPECT_EQ(vpi_register_cb(nullptr), nullptr);

  EXPECT_EQ(vpi_register_systf(nullptr), nullptr);

  EXPECT_EQ(vpi_remove_cb(nullptr), 0);

  EXPECT_EQ(vpi_get_vlog_info(nullptr), 0);

  EXPECT_EQ(vpi_compare_objects(nullptr, nullptr), 0);
}

TEST_F(VpiArgumentConventions, ChkErrorAcceptsNullErrorInfo) {
  RaiseError();

  s_vpi_error_info info = {};
  int with_structure = vpi_chk_error(&info);
  ASSERT_EQ(with_structure, vpiError);

  EXPECT_EQ(vpi_chk_error(nullptr), vpiError);
}

TEST_F(VpiArgumentConventions,
       AReferenceObjectMayBeOmittedWhereADiagramSaysSo) {
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  EXPECT_NE(vpi_iterate(vpiCallback, nullptr), nullptr);

  EXPECT_EQ(vpi_handle(vpiSysTfCall, nullptr), nullptr);
}

TEST_F(VpiArgumentConventions, AReferenceObjectIsMandatoryWhereNoneSaysSo) {
  EXPECT_EQ(vpi_handle(vpiParent, nullptr), nullptr);

  EXPECT_EQ(vpi_iterate(vpiPort, nullptr), nullptr);
}

}  // namespace
}  // namespace delta
