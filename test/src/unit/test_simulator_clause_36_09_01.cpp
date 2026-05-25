#include <gtest/gtest.h>

#include "simulator/vpi.h"

namespace delta {
namespace {

class UserDefinedSystfRegistration : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// §36.9.1: a user-defined system task or system function name shall begin
// with a dollar sign. A name lacking the leading '$' is not a legal
// user-defined name, so registration of it must be refused.
TEST_F(UserDefinedSystfRegistration, NameWithoutDollarIsRejected) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "missing_dollar";

  vpiHandle h = vpi_register_systf(&data);

  EXPECT_EQ(h, nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
}

// §36.9.1: a name beginning with the dollar sign is the legal form, so the
// same registration succeeds once the leading '$' is present.
TEST_F(UserDefinedSystfRegistration, NameWithDollarIsAccepted) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$get_vector";

  vpiHandle h = vpi_register_systf(&data);

  ASSERT_NE(h, nullptr);
  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 1);
  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[0].tfname, "$get_vector");
}

// §36.9.1: a name shall begin with a dollar sign. A null name string carries
// no leading '$' at all, so registration must be refused rather than
// dereferencing into it.
TEST_F(UserDefinedSystfRegistration, NullNameIsRejected) {
  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.tfname = nullptr;

  vpiHandle h = vpi_register_systf(&data);

  EXPECT_EQ(h, nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
}

// §36.9.1: the registration of system tasks shall occur prior to elaboration
// or the resolution of references. Before elaboration begins, registration is
// permitted.
TEST_F(UserDefinedSystfRegistration, RegistrationBeforeElaborationSucceeds) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$early";

  vpiHandle h = vpi_register_systf(&data);

  ASSERT_NE(h, nullptr);
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs().size(), 1);
}

// §36.9.1: once elaboration (or reference resolution) has begun, the window
// for registering system tasks and functions has closed, so a later
// registration must be refused.
TEST_F(UserDefinedSystfRegistration, RegistrationAfterElaborationIsRejected) {
  vpi_ctx_.MarkElaborationStarted();

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$late";

  vpiHandle h = vpi_register_systf(&data);

  EXPECT_EQ(h, nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
}

}  // namespace
}  // namespace delta
