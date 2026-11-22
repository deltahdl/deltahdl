#include <gtest/gtest.h>

#include <map>
#include <string>
#include <string_view>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

std::map<std::string, double>& ScaledTimes() {
  static std::map<std::string, double> times;
  return times;
}

double ScaledTimeOf(vpiHandle obj) {
  s_vpi_time time = {};
  time.type = vpiScaledRealTime;
  vpi_get_time(obj, &time);
  return time.real;
}

vpiHandle FirstNamed(PLI_INT32 type, vpiHandle parent, std::string_view name) {
  vpiHandle it = vpi_iterate(type, parent);
  if (it == nullptr) return nullptr;
  while (vpiHandle obj = vpi_scan(it)) {
    if (name == vpi_get_str(vpiName, obj)) {
      vpi_release_handle(it);
      return obj;
    }
  }
  return nullptr;
}

void ReadTheCompilationUnitsTimes() {
  vpiHandle unit = FirstNamed(vpiPackage, nullptr, "$unit");
  ScaledTimes()["$unit"] = unit != nullptr ? ScaledTimeOf(unit) : -1.0;
  vpiHandle var =
      unit != nullptr ? FirstNamed(vpiVariables, unit, "unit_v") : nullptr;
  ScaledTimes()["unit_v"] = var != nullptr ? ScaledTimeOf(var) : -1.0;
}

PLI_INT32 ReadEachScopesTimeCalltf(PLI_BYTE8*) {
  for (const char* name : {"top.i", "top.i.iv", "top.g", "top.g.gv", "p",
                           "p::pv", "top.t", "top.f"}) {
    vpiHandle obj = vpi_handle_by_name(VpiText(name), nullptr);
    ScaledTimes()[name] = obj != nullptr ? ScaledTimeOf(obj) : -1.0;
  }
  ReadTheCompilationUnitsTimes();
  vpiHandle slots = vpi_iterate(vpiTimeQueue, nullptr);
  vpiHandle slot = slots != nullptr ? vpi_scan(slots) : nullptr;
  ScaledTimes()["queue"] = slot != nullptr ? ScaledTimeOf(slot) : -1.0;
  if (slot != nullptr) vpi_release_handle(slots);
  return 0;
}

class TimeOfEachScope : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    ScaledTimes().clear();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$times");
    data.calltf = &ReadEachScopesTimeCalltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
    Run("timeunit 1us; timeprecision 1ps;\n"
        "logic unit_v;\n"
        "package p; timeunit 10ns; timeprecision 1ps; logic pv; endpackage\n"
        "interface ifc; timeunit 100ps; timeprecision 1ps; logic iv;\n"
        "endinterface\n"
        "program prg; timeunit 1ps; timeprecision 1ps; logic gv; endprogram\n"
        "module top; timeunit 1ns; timeprecision 1ps;\n"
        "  logic later;\n"
        "  ifc i(); prg g();\n"
        "  task automatic t; endtask\n"
        "  function void f; endfunction\n"
        "  initial #7 $times;\n"
        "  initial #12 later = 1;\n"
        "endmodule\n");
  }

  static double TimeOf(const char* name) { return ScaledTimes()[name]; }
};

TEST_F(TimeOfEachScope, AnInterfaceAndItsVariableReadInItsUnit) {
  EXPECT_DOUBLE_EQ(TimeOf("top.i"), 70.0);
  EXPECT_DOUBLE_EQ(TimeOf("top.i.iv"), 70.0);
}

TEST_F(TimeOfEachScope, AProgramAndItsVariableReadInItsUnit) {
  EXPECT_DOUBLE_EQ(TimeOf("top.g"), 7000.0);
  EXPECT_DOUBLE_EQ(TimeOf("top.g.gv"), 7000.0);
}

TEST_F(TimeOfEachScope, DISABLED_APackageAndItsVariableReadInItsUnit) {
  EXPECT_DOUBLE_EQ(TimeOf("p"), 0.7);
  EXPECT_DOUBLE_EQ(TimeOf("p::pv"), 0.7);
}

TEST_F(TimeOfEachScope,
       DISABLED_TheCompilationUnitAndItsVariableReadInItsUnit) {
  EXPECT_DOUBLE_EQ(TimeOf("$unit"), 0.007);
  EXPECT_DOUBLE_EQ(TimeOf("unit_v"), 0.007);
}

TEST_F(TimeOfEachScope, ATaskAndFunctionReadInTheirModulesUnit) {
  EXPECT_DOUBLE_EQ(TimeOf("top.t"), 7.0);
  EXPECT_DOUBLE_EQ(TimeOf("top.f"), 7.0);
}

TEST_F(TimeOfEachScope, ATimeQueueOfARunReadsInTheSimulationUnit) {
  EXPECT_DOUBLE_EQ(TimeOf("queue"), 12000.0);
}

}  // namespace
}  // namespace delta
