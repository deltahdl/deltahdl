#pragma once

#include <cstdint>
#include <string_view>
#include <utility>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

// Elaborates, lowers, and runs `src`, then returns the unsigned value of the
// single variable `var`. The design and the variable are checked non-null with
// non-fatal expectations so callers can keep asserting on the returned value.
inline uint64_t RunModule(SimFixture& f, const char* src,
                          std::string_view var) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable(var);
  EXPECT_NE(v, nullptr);
  return v ? v->value.ToUint64() : 0;
}

// Elaborates, lowers, and runs `src` without fetching any variable. The design
// is checked non-null (non-fatal) so callers can keep asserting on the
// fixture's diagnostics (e.g. warning counts) after the run completes.
inline void RunModuleNoVar(SimFixture& f, const char* src) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
}

// Elaborates, lowers, and runs `src`, returning the elaborated design so
// callers can apply their own (fatal) non-null assertion and then read an
// arbitrary set of variables off the fixture. Shares the common
// elaborate/lower/run sequence used by tests that inspect three or more result
// variables.
inline RtlirDesign* ElaborateLowerRun(SimFixture& f, const char* src) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return design;
}

// Elaborates, lowers, and runs `src`, then returns the unsigned values of the
// two variables `v1` and `v2`. The design and both variables are asserted
// non-null (fatal), matching the run-and-check-two-variables pattern shared by
// the randsequence, expression, and IPC tests.
inline std::pair<uint64_t, uint64_t> RunModuleTwoVars(SimFixture& f,
                                                      const char* src,
                                                      std::string_view v1,
                                                      std::string_view v2) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var1 = f.ctx.FindVariable(v1);
  auto* var2 = f.ctx.FindVariable(v2);
  EXPECT_NE(var1, nullptr);
  EXPECT_NE(var2, nullptr);
  uint64_t a = var1 ? var1->value.ToUint64() : 0;
  uint64_t b = var2 ? var2->value.ToUint64() : 0;
  return {a, b};
}
