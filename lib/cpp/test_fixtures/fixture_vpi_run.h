#pragma once

#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "simulator/sv_vpi_user.h"
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

  // The names of the objects of `type` `ref` reaches, sorted. An object of no
  // name, such as the property inst an assertion's spec holds, which a
  // vpiAssertion iteration of an instance reaches as an assertion (§37.49,
  // §39.3.1), contributes none.
  static std::vector<std::string> NamesOf(int type, vpiHandle ref) {
    std::vector<std::string> names;
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return names;
    while (vpiHandle obj = vpi_scan(it)) {
      const char* name = vpi_get_str(vpiName, obj);
      if (name != nullptr) names.emplace_back(name);
    }
    std::ranges::sort(names);
    return names;
  }

  // The object of `type` named `name` that `ref` reaches, passing over those
  // of no name; null for none.
  static vpiHandle Named(int type, vpiHandle ref, std::string_view name) {
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return nullptr;
    while (vpiHandle obj = vpi_scan(it)) {
      const char* own = vpi_get_str(vpiName, obj);
      if (own != nullptr && name == own) return obj;
    }
    return nullptr;
  }

  // §37.50 and §37.52: the property expr the property spec of the assertion
  // `name` of `top` reaches, null for none.
  static vpiHandle PropertyOf(const char* name) {
    vpiHandle assertion = Named(vpiAssertion, By("top"), name);
    vpiHandle spec =
        assertion == nullptr ? nullptr : vpi_handle(vpiProperty, assertion);
    return spec == nullptr ? nullptr : vpi_handle(vpiPropertyExpr, spec);
  }

  // §37.59: the operator of the operation `op`, 0 where it is no operation.
  static int OpOf(vpiHandle op) {
    if (op == nullptr || vpi_get(vpiType, op) != vpiOperation) return 0;
    return vpi_get(vpiOpType, op);
  }

  // The operands of `op` in the order vpiOperand reaches them.
  static std::vector<vpiHandle> OperandsOf(vpiHandle op) {
    std::vector<vpiHandle> operands;
    vpiHandle it = op == nullptr ? nullptr : vpi_iterate(vpiOperand, op);
    if (it == nullptr) return operands;
    for (vpiHandle h = vpi_scan(it); h != nullptr; h = vpi_scan(it)) {
      operands.push_back(h);
    }
    return operands;
  }

  // The object `name` reaches from the top of the design, null for none.
  static vpiHandle By(const std::string& name) {
    return vpi_handle_by_name(VpiText(name.c_str()), nullptr);
  }

  // The kinds of the objects of `type` `ref` reaches, in the order reached.
  static std::vector<int> KindsOf(int type, vpiHandle ref) {
    std::vector<int> kinds;
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return kinds;
    while (vpiHandle obj = vpi_scan(it)) kinds.push_back(vpi_get(vpiType, obj));
    return kinds;
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
