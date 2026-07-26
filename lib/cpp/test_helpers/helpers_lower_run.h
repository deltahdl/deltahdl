#pragma once

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <string>
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

// Elaborates, lowers, and runs `src`, then checks the leading elements of the
// unpacked array `name` against `expected`, in index order. A source whose
// every iteration writes one element -- a generate loop over a genvar, say --
// states what it produced as the whole list rather than naming each element
// separately, so the expectation reads as the sequence the run was meant to
// leave behind. Each element is asserted to exist (fatal) before its value is
// read.
inline void RunModuleArray(SimFixture& f, const char* src,
                           std::string_view name,
                           std::initializer_list<uint64_t> expected) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  size_t i = 0;
  for (uint64_t want : expected) {
    auto element = std::string(name) + "[" + std::to_string(i) + "]";
    auto* v = f.ctx.FindVariable(element);
    ASSERT_NE(v, nullptr) << element;
    EXPECT_EQ(v->value.ToUint64(), want) << element;
    ++i;
  }
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

// Runs `src` twice, each time in a simulation context of its own, and returns
// the value variable `name` was left holding -- after checking the two runs
// agree on it.
//
// A run that draws on a random number generator is still expected to produce
// the same result every time it is replayed from the same starting state, so a
// test states what the value has to be once and lets the second run stand for
// the replay. The value is 0 when either run failed to elaborate.
inline uint64_t RunTwiceForSameValue(const char* src, std::string_view name) {
  SimFixture f1;
  auto* d1 = ElaborateSrc(src, f1);
  EXPECT_NE(d1, nullptr);
  if (d1 == nullptr) return 0;
  LowerAndRun(d1, f1);
  EXPECT_FALSE(f1.has_errors);

  SimFixture f2;
  auto* d2 = ElaborateSrc(src, f2);
  EXPECT_NE(d2, nullptr);
  if (d2 == nullptr) return 0;
  LowerAndRun(d2, f2);
  EXPECT_FALSE(f2.has_errors);

  auto* v1 = f1.ctx.FindVariable(name);
  auto* v2 = f2.ctx.FindVariable(name);
  EXPECT_NE(v1, nullptr);
  EXPECT_NE(v2, nullptr);
  if (v1 == nullptr || v2 == nullptr) return 0;
  EXPECT_EQ(v1->value.ToUint64(), v2->value.ToUint64());
  return v1->value.ToUint64();
}
