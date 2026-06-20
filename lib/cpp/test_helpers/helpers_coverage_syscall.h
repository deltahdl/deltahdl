#pragma once

#include <cstdint>
#include <string_view>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

// Evaluates $<syscall>(coverage_type, "name") through the production expression
// evaluator (EvalExpr) and returns the reported §40.3.1 status value as a
// signed integer, matching how a real $coverage_* system function reports.
inline int RunCoverageSysCall(SimFixture& f, std::string_view syscall,
                              int coverage_type, std::string_view name) {
  auto* call = MkSysCall(f.arena, syscall,
                         {MkInt(f.arena, static_cast<uint64_t>(coverage_type)),
                          MkStr(f.arena, name)});
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

// Evaluates $coverage_merge(coverage_type, "name") (§40.3.2.4) through the
// production evaluator and returns the reported value as a signed integer.
inline int RunMerge(SimFixture& f, int coverage_type, std::string_view name) {
  return RunCoverageSysCall(f, "$coverage_merge", coverage_type, name);
}
