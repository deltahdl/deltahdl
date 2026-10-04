#pragma once

#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

// A design elaborated and run while a PLI application is registered, which is
// what has a run build its VPI model (AttachDesignToPliApplications), for a
// case that reads the model back once the run is over: the object kinds §37
// draws are built from a real design here rather than by hand.

namespace delta {

inline PLI_INT32 VpiDesignRunCalltf(PLI_BYTE8* /*user_data*/) { return 0; }

// A design run with a PLI application registered, which is what has the run
// build its VPI model, read back from the test once the run is over.
class VpiDesignRun : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&vpi_);
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$noop");
    data.calltf = &VpiDesignRunCalltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  void Run(const std::string& src) {
    RtlirDesign* design = ElaborateSrc(src, f_);
    ASSERT_NE(design, nullptr);
    ASSERT_FALSE(f_.has_errors);
    LowerAndRun(design, f_);
  }

  // The names of the objects of `type` `ref` reaches, sorted.
  static std::vector<std::string> NamesOf(int type, vpiHandle ref) {
    std::vector<std::string> names;
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return names;
    while (vpiHandle obj = vpi_scan(it)) {
      names.emplace_back(vpi_get_str(vpiName, obj));
    }
    std::ranges::sort(names);
    return names;
  }

  // The object of `type` named `name` that `ref` reaches; null for none.
  static vpiHandle Named(int type, vpiHandle ref, std::string_view name) {
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return nullptr;
    while (vpiHandle obj = vpi_scan(it)) {
      if (name == vpi_get_str(vpiName, obj)) return obj;
    }
    return nullptr;
  }

  // The full name of the child of `scope` named `name`, read off the object.
  static std::string FullNameOfChild(vpiHandle scope, std::string_view name) {
    for (VpiObject* child : VpiObjectOf(scope)->children) {
      if (child->name == name) return child->full_name;
    }
    return "";
  }

  VpiContext vpi_;
  SimFixture f_;
};

}  // namespace delta
