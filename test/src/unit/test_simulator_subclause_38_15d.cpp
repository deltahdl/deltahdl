#include <gtest/gtest.h>

#include <map>
#include <string>
#include <utility>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

int IntOf(vpiHandle obj) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = -1;
  vpi_get_value(obj, &value);
  return value.value.integer;
}

std::vector<int>& ArgumentsRead() {
  static std::vector<int> read;
  return read;
}

PLI_INT32 ReadArgumentCalltf(PLI_BYTE8*) {
  vpiHandle args = vpi_iterate(vpiArgument, vpi_handle(vpiSysTfCall, nullptr));
  if (args == nullptr) return 0;
  vpiHandle first = vpi_scan(args);
  if (first != nullptr) {
    vpi_release_handle(args);
    ArgumentsRead().push_back(IntOf(first));
  }
  return 0;
}

class SideEffectsOfARead : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    ArgumentsRead().clear();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$probe");
    data.calltf = &ReadArgumentCalltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  static vpiHandle RhsOfUntakenBranch(vpiHandle process) {
    vpiHandle branch = vpi_handle(vpiStmt, vpi_handle(vpiStmt, process));
    return branch != nullptr ? vpi_handle(vpiRhs, branch) : nullptr;
  }
};

TEST_F(SideEffectsOfARead, AnIncrementReturnsTheOldValueAndIncrementsOnce) {
  Run("module top; int i = 5;\n"
      "  initial $probe(i++);\n"
      "endmodule\n");
  EXPECT_EQ(ArgumentsRead(), (std::vector<int>{5}));
  EXPECT_EQ(IntOf(By("top.i")), 6);
}

TEST_F(SideEffectsOfARead, AnIndexCallingAFunctionCallsItOnce) {
  Run("module top; int count = 0;\n"
      "  logic [7:0] x [4] = '{8'h10, 8'h20, 8'h30, 8'h40};\n"
      "  function automatic int pick(); count++; return 2; endfunction\n"
      "  initial $probe(x[pick()]);\n"
      "endmodule\n");
  EXPECT_EQ(ArgumentsRead(), (std::vector<int>{0x30}));
  EXPECT_EQ(IntOf(By("top.count")), 1);
}

TEST_F(SideEffectsOfARead, AnExpressionOfTheHierarchyIsEvaluatedWithItsEffect) {
  Run("module top; int i = 5, count = 0, y = 0;\n"
      "  function automatic int pick(); count++; return 2; endfunction\n"
      "  initial if (y == 99) y = pick();\n"
      "  initial if (y == 99) y = i++;\n"
      "endmodule\n");
  const std::vector<vpiHandle> kProcesses = ObjectsOf(vpiProcess, By("top"));
  ASSERT_EQ(kProcesses.size(), 2u);
  vpiHandle call = RhsOfUntakenBranch(kProcesses[0]);
  vpiHandle increment = RhsOfUntakenBranch(kProcesses[1]);
  ASSERT_NE(call, nullptr);
  ASSERT_NE(increment, nullptr);
  EXPECT_EQ(IntOf(call), 2);
  EXPECT_EQ(IntOf(By("top.count")), 1);
  EXPECT_EQ(IntOf(increment), 5);
  EXPECT_EQ(IntOf(By("top.i")), 6);
}

struct ChangeSeen {
  bool allocated = false;
  std::vector<PLI_UINT32> words;
};

ChangeSeen& SeenChange() {
  static ChangeSeen seen;
  return seen;
}

PLI_INT32 VectorChangeRoutine(p_cb_data data) {
  if (data->value == nullptr || data->value->format != vpiVectorVal) return 0;
  ChangeSeen& seen = SeenChange();
  seen.allocated = data->value->value.vector != nullptr;
  seen.words.clear();
  if (!seen.allocated) return 0;
  for (int k = 0; k < 2; ++k) {
    seen.words.push_back(data->value->value.vector[k].aval);
    seen.words.push_back(data->value->value.vector[k].bval);
  }
  return 0;
}

PLI_INT32 WatchCalltf(PLI_BYTE8*) {
  static s_vpi_time time = {vpiSuppressTime, 0, 0, 0.0};
  static s_vpi_value value = {};
  value = {};
  value.format = vpiVectorVal;
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = &VectorChangeRoutine;
  cb.obj = vpi_handle_by_name(VpiText("top.v"), nullptr);
  cb.time = &time;
  cb.value = &value;
  vpi_register_cb(&cb);
  return 0;
}

std::map<std::string, int>& Sampled() {
  static std::map<std::string, int> sampled;
  return sampled;
}

PLI_INT32 SampleCalltf(PLI_BYTE8*) {
  for (const char* name : {"top.vn", "p::pv", "top.i.iv", "top.g.gv"}) {
    vpiHandle obj = vpi_handle_by_name(VpiText(name), nullptr);
    Sampled()[name] = obj != nullptr ? IntOf(obj) : -1;
  }
  return 0;
}

class ValuesDuringARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    SeenChange() = {};
    Sampled().clear();
    for (const auto& [name, calltf] : {std::pair{"$watch", &WatchCalltf},
                                       std::pair{"$sample", &SampleCalltf}}) {
      s_vpi_systf_data data = {};
      data.type = vpiSysTask;
      data.tfname = VpiText(name);
      data.calltf = calltf;
      ASSERT_NE(vpi_register_systf(&data), nullptr);
    }
  }
};

TEST_F(ValuesDuringARun, AVectorChangeArrivesInAnArrayTheSimulatorAllocated) {
  Run("module top; logic [39:0] v = 0;\n"
      "  initial begin $watch; #1 v = 40'hx5_DEADBEEF; end\n"
      "endmodule\n");
  EXPECT_TRUE(SeenChange().allocated);
  EXPECT_EQ(SeenChange().words,
            (std::vector<PLI_UINT32>{0xDEADBEEFu, 0u, 0xF5u, 0xF0u}));
}

TEST_F(ValuesDuringARun, EachKindOfObjectReadsItsCurrentValue) {
  Run("package p; int pv = 0; endpackage\n"
      "interface ifc; int iv = 0; endinterface\n"
      "program prg; int gv = 0; initial begin #1 gv = 33; #5; end endprogram\n"
      "module top; logic [7:0] r = 0; wire [7:0] vn = r;\n"
      "  ifc i(); prg g();\n"
      "  initial begin\n"
      "    #1 r = 8'h5A; p::pv = 11; i.iv = 22;\n"
      "    #1 $sample;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(Sampled(), (std::map<std::string, int>{{"p::pv", 11},
                                                   {"top.g.gv", 33},
                                                   {"top.i.iv", 22},
                                                   {"top.vn", 0x5A}}));
}

class UdpEntryOfFiveSymbols : public VpiDesignRun {};

TEST_F(UdpEntryOfFiveSymbols, TheFifthSymbolOpensTheSecondElement) {
  Run("primitive latch3(q, a, b, c);\n"
      "  output reg q; input a, b, c;\n"
      "  table r 0 1 : 0 : x; endtable\n"
      "endprimitive\n"
      "module top; reg a, b, c; wire q; latch3 u(q, a, b, c); endmodule\n");
  const std::vector<vpiHandle> kRows =
      ObjectsOf(vpiTableEntry, Named(vpiUdpDefn, nullptr, "latch3"));
  ASSERT_EQ(kRows.size(), 1u);
  s_vpi_value value = {};
  value.format = vpiVectorVal;
  vpi_get_value(kRows[0], &value);
  ASSERT_NE(value.value.vector, nullptr);
  EXPECT_EQ(value.value.vector[0].aval, 0x72003000u);
  EXPECT_EQ(value.value.vector[0].bval, 0x31003000u);
  EXPECT_EQ(value.value.vector[1].aval, 0x78000000u);
  EXPECT_EQ(value.value.vector[1].bval, 0u);
}

}  // namespace
}  // namespace delta
