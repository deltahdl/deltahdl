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

namespace delta {

inline PLI_INT32 VpiDesignRunCalltf(PLI_BYTE8*) { return 0; }

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

  static vpiHandle Named(int type, vpiHandle ref, std::string_view name) {
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return nullptr;
    while (vpiHandle obj = vpi_scan(it)) {
      const char* own = vpi_get_str(vpiName, obj);
      if (own != nullptr && name == own) return obj;
    }
    return nullptr;
  }

  static std::vector<vpiHandle> ObjectsOf(int type, vpiHandle ref) {
    std::vector<vpiHandle> objects;
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return objects;
    while (vpiHandle obj = vpi_scan(it)) objects.push_back(obj);
    return objects;
  }

  static std::string CalleeOf(vpiHandle call) {
    for (const int kRelation : {vpiTask, vpiFunction}) {
      vpiHandle called = vpi_handle(kRelation, call);
      if (called != nullptr) return vpi_get_str(vpiName, called);
    }
    const char* decompile = vpi_get_str(vpiDecompile, call);
    if (decompile == nullptr) return "";
    const std::string_view kText(decompile);
    return std::string(kText.substr(0, kText.find('(')));
  }

  static vpiHandle CallOf(int type, vpiHandle ref, std::string_view callee) {
    for (vpiHandle call : ObjectsOf(type, ref)) {
      if (CalleeOf(call) == callee) return call;
    }
    return nullptr;
  }

  static std::string ActionReached(int relation, vpiHandle ref) {
    vpiHandle reached = ref == nullptr ? nullptr : vpi_handle(relation, ref);
    return reached == nullptr ? "" : CalleeOf(reached);
  }

  static vpiHandle PropertyOf(const char* name) {
    vpiHandle assertion = Named(vpiAssertion, By("top"), name);
    vpiHandle spec =
        assertion == nullptr ? nullptr : vpi_handle(vpiProperty, assertion);
    return spec == nullptr ? nullptr : vpi_handle(vpiPropertyExpr, spec);
  }

  static int OpOf(vpiHandle op) {
    if (op == nullptr || vpi_get(vpiType, op) != vpiOperation) return 0;
    return vpi_get(vpiOpType, op);
  }

  static std::vector<vpiHandle> OperandsOf(vpiHandle op) {
    std::vector<vpiHandle> operands;
    vpiHandle it = op == nullptr ? nullptr : vpi_iterate(vpiOperand, op);
    if (it == nullptr) return operands;
    for (vpiHandle h = vpi_scan(it); h != nullptr; h = vpi_scan(it)) {
      operands.push_back(h);
    }
    return operands;
  }

  static vpiHandle By(const std::string& name) {
    return vpi_handle_by_name(VpiText(name.c_str()), nullptr);
  }

  static std::vector<int> KindsOf(int type, vpiHandle ref) {
    std::vector<int> kinds;
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return kinds;
    while (vpiHandle obj = vpi_scan(it)) kinds.push_back(vpi_get(vpiType, obj));
    return kinds;
  }

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
