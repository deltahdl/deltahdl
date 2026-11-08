#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <string>
#include <utility>

#include "common/diagnostic.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

inline void ExpectRunReportedNoError(const SimFixture& f, size_t before) {
  const auto& diags = f.diag.Diagnostics();
  for (size_t i = before; i < diags.size(); ++i) {
    if (diags[i].severity != DiagSeverity::kError) continue;
    ADD_FAILURE() << "the run reported: " << diags[i].message;
  }
}

inline uint64_t RunAndGet(const std::string& src, const char* var_name) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  if (!design) return 0;
  size_t before = f.diag.Diagnostics().size();
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
  ExpectRunReportedNoError(f, before);
  auto* var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var) return 0;
  return var->value.ToUint64();
}

inline double RunAndGetReal(const std::string& src, const char* var_name) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  if (!design) return 0.0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
  auto* var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var) return 0.0;
  return RealVecToDouble(var->value);
}

inline void LowerRunAndCheck(
    SimFixture& f, RtlirDesign* design,
    std::initializer_list<std::pair<const char*, uint64_t>> checks) {
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
  for (auto& [name, expected] : checks) {
    auto* var = f.ctx.FindVariable(name);
    ASSERT_NE(var, nullptr) << "Variable not found: " << name;
    EXPECT_EQ(var->value.ToUint64(), expected) << "Variable: " << name;
  }
}
