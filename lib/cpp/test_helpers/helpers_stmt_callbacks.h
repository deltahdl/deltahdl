#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <set>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "preprocessor/protect_processing.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {

struct StmtCall {
  int type = 0;
  uint32_t now = 0;
  bool operator==(const StmtCall&) const = default;
};

inline std::vector<StmtCall>& StmtCalls() {
  static std::vector<StmtCall> calls;
  return calls;
}

inline std::string& WatchedModule() {
  static std::string name = "top";
  return name;
}

inline vpiHandle& ModuleWideStmtCallback() {
  static vpiHandle handle = nullptr;
  return handle;
}

inline PLI_INT32 RecordStmtCall(p_cb_data cb) {
  StmtCalls().push_back(
      {vpi_get(vpiType, cb->obj), cb->time != nullptr ? cb->time->low : 0});
  return 0;
}

inline PLI_INT32 PlaceModuleWideStmtCallback(p_cb_data) {
  static s_vpi_time sim_time = {vpiSimTime, 0, 0, 0};
  s_cb_data data = {};
  data.reason = cbStmt;
  data.cb_rtn = &RecordStmtCall;
  data.obj = vpi_handle_by_name(VpiText(WatchedModule().c_str()), nullptr);
  data.time = &sim_time;
  ModuleWideStmtCallback() = vpi_register_cb(&data);
  return 0;
}

inline void WatchStatementsOf(const char* module) {
  StmtCalls().clear();
  ModuleWideStmtCallback() = nullptr;
  WatchedModule() = module;
  s_cb_data data = {};
  data.reason = cbStartOfSimulation;
  data.cb_rtn = &PlaceModuleWideStmtCallback;
  ASSERT_NE(vpi_register_cb(&data), nullptr);
}

inline std::vector<int> StmtTypesCalled() {
  std::vector<int> types;
  for (const StmtCall& call : StmtCalls()) types.push_back(call.type);
  return types;
}

inline std::vector<int> StmtTypesCalledAmong(const std::set<int>& kept) {
  std::vector<int> types;
  for (const StmtCall& call : StmtCalls()) {
    if (kept.contains(call.type)) types.push_back(call.type);
  }
  return types;
}

constexpr const char* kSealedStatementsKey = "statement-callback-key";

inline std::string SealedStatementsDesign() {
  return EncryptEnvelopes(
      "module t; int a, b;\n"
      "`pragma protect begin\n"
      "  initial begin : sealed a = 1; end\n"
      "`pragma protect end\n"
      "  initial begin : clear b = 2; end\n"
      "endmodule\n",
      kSealedStatementsKey);
}

class StmtCallbacksOfARun : public VpiDesignRun {
 protected:
  void RunWatchingTop(const std::string& src) {
    WatchStatementsOf("top");
    Run(src);
  }
};

}  // namespace delta
