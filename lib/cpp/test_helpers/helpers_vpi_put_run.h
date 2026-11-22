#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <functional>

#include "fixture_vpi_run.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {

inline std::function<void()>& Putter() {
  static std::function<void()> putter;
  return putter;
}

inline PLI_INT32 PutterCalltf(PLI_BYTE8*) {
  Putter()();
  return 0;
}

class VpiPutRun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Putter() = [] {};
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$put");
    data.calltf = &PutterCalltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  static int IntOf(const char* name) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(By(name), &value);
    return value.value.integer;
  }
};

inline vpiHandle PutIntAt(const char* name, int value, int flags,
                          s_vpi_time* time) {
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = value;
  return vpi_put_value(vpi_handle_by_name(VpiText(name), nullptr), &val, time,
                       flags);
}

inline vpiHandle PutInt(const char* name, int value, int flags,
                        uint32_t delay = 0) {
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = delay;
  return PutIntAt(name, value, flags, &time);
}

}  // namespace delta
