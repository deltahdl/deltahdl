#include <gtest/gtest.h>

#include "fixture_vpi_run.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

PLI_INT32 read_returned = -1;
PLI_INT32 read_level = -1;

PLI_INT32 ReadSavedDataCalltf(PLI_BYTE8*) {
  char buf[4] = {};
  read_returned = vpi_get_data(31, buf, 2);
  read_level = vpi_chk_error(nullptr);
  return 0;
}

class SaveDataOfARun : public VpiDesignRun {};

TEST_F(SaveDataOfARun, ACalltfIsRefusedTheSavedData) {
  read_returned = -1;
  read_level = -1;
  vpi_.SeedSaveData(31, "ok", 2);
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &ReadSavedDataCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  Run("module top; initial $probe; endmodule\n");
  EXPECT_EQ(read_returned, 0);
  EXPECT_EQ(read_level, vpiError);
}

}  // namespace
}  // namespace delta
