#pragma once

#include <gtest/gtest.h>

#include <fstream>
#include <sstream>
#include <string>

#include "fixture_scratch_dir.h"
#include "fixture_vpi_run.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

// A run whose design opens files by relative names, in a working directory of
// its own, and whose system tasks reach the descriptors it opened through VPI:
// the §38.24 to §38.28 routines over the descriptors $fopen returns (§21.3.1).
class RunFilesRun : public delta::VpiDesignRun {
 protected:
  // Registers the system task `name` running `calltf`.
  static void RegisterTask(const char* name, PLI_INT32 (*calltf)(PLI_BYTE8*)) {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = delta::VpiText(name);
    data.calltf = calltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  // The descriptor the integer variable `name` of the run holds.
  static PLI_UINT32 DescriptorIn(const char* name) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(vpi_handle_by_name(delta::VpiText(name), nullptr), &value);
    return static_cast<PLI_UINT32>(value.value.integer);
  }

  // The text of the file `name` in the run's directory, empty for none.
  std::string FileText(const std::string& name) const {
    std::ifstream file(scratch_.dir / name);
    std::stringstream text;
    text << file.rdbuf();
    return text.str();
  }

 private:
  ScratchWorkingDir scratch_;
};
