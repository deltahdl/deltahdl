#pragma once

#include <gtest/gtest.h>

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

inline void RunModuleNoVar(SimFixture& f, const char* src) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
}

inline RtlirDesign* ElaborateLowerRun(SimFixture& f, const char* src) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return design;
}

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
