#include <gtest/gtest.h>

#include "helpers_run_files.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct CalltfWrite {
  PLI_INT32 returned = -1;
  PLI_INT32 error_level = 0;
  PLI_INT32 read_back = -1;
};

CalltfWrite results;

class PutDataInARun : public RunFilesRun {
 protected:
  void SetUp() override {
    RunFilesRun::SetUp();
    results = {};
  }

  static PLI_INT32 WriteFromCalltf(PLI_BYTE8*) {
    results.returned = vpi_put_data(15, VpiText("abcd"), 4);
    s_vpi_error_info info = {};
    const PLI_INT32 kLevel = vpi_chk_error(&info);
    results.error_level = kLevel;
    return 0;
  }

  static PLI_INT32 ReadInRestart(s_cb_data*) {
    char buf[8] = {};
    results.read_back = vpi_get_data(15, buf, 4);
    return 0;
  }
};

TEST_F(PutDataInARun, RejectedInsideACalltfRoutine) {
  RegisterTask("$write_data", &WriteFromCalltf);
  Run("module top; initial $write_data; endmodule\n");
  EXPECT_EQ(results.returned, 0);
  EXPECT_EQ(results.error_level, vpiError);
  s_cb_data reg = {};
  reg.reason = cbStartOfRestart;
  reg.cb_rtn = &ReadInRestart;
  ASSERT_NE(vpi_register_cb(&reg), nullptr);
  vpi_.DispatchCallbacks(cbStartOfRestart);
  EXPECT_EQ(results.read_back, 0);
}

}  // namespace
}  // namespace delta
