// §38.37: vpi_register_systf

#include <gtest/gtest.h>

#include "simulation/vpi.h"

namespace delta {
namespace {

class VpiClause3837Test : public ::testing::Test {
protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(VpiClause3837Test, RegisterSystfStoresTask) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$hello";
  vpi_register_systf(&data);

  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 1);
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[0].type, vpiSysTask);
  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[0].tfname, "$hello");
}

TEST_F(VpiClause3837Test, RegisterMultipleSystfs) {
  s_vpi_systf_data data1 = {};
  data1.type = vpiSysTask;
  data1.tfname = "$task_a";

  s_vpi_systf_data data2 = {};
  data2.type = vpiSysFunc;
  data2.tfname = "$func_b";

  vpi_register_systf(&data1);
  vpi_register_systf(&data2);

  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 2);
  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[0].tfname, "$task_a");
  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[1].tfname, "$func_b");
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[1].type, vpiSysFunc);
}

TEST_F(VpiClause3837Test, RegisterSystfNullptrDoesNotCrash) {
  vpiHandle h = vpi_register_systf(nullptr);
  EXPECT_EQ(h, nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
}

} // namespace
} // namespace delta
