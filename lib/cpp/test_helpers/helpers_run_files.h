#pragma once

#include <gtest/gtest.h>

#include <fstream>
#include <sstream>
#include <string>

#include "fixture_scratch_dir.h"
#include "fixture_vpi_run.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

class RunFilesRun : public delta::VpiDesignRun {
 protected:
  static void RegisterTask(const char* name, PLI_INT32 (*calltf)(PLI_BYTE8*)) {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = delta::VpiText(name);
    data.calltf = calltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  static PLI_UINT32 DescriptorIn(const char* name) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(vpi_handle_by_name(delta::VpiText(name), nullptr), &value);
    return static_cast<PLI_UINT32>(value.value.integer);
  }

  std::string FileText(const std::string& name) const {
    std::ifstream file(scratch_.dir / name);
    std::stringstream text;
    text << file.rdbuf();
    return text.str();
  }

 private:
  ScratchWorkingDir scratch_;
};
