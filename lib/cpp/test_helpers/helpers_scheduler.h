#pragma once

#include <cstdint>
#include <initializer_list>
#include <string>
#include <utility>

#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

// Elaborates, lowers and runs `src`, then returns the value the run left in the
// variable `var_name`.
//
// The elaboration is required to be clean, not merely to have produced
// something. Elaboration reports what the source got wrong and still hands back
// a design, and the evaluator will happily run that design and leave a value
// behind, so a caller that read the value alone could not tell source the
// elaborator accepted from source it rejected -- it would be asserting on
// whatever the evaluator made of a program that will not elaborate. The fixture
// already records the verdict; this reads it.
inline uint64_t RunAndGet(const std::string& src, const char* var_name) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  if (!design) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
  auto* var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var) return 0;
  return var->value.ToUint64();
}

// The real-valued form of RunAndGet, decoding the variable's bits through
// RealVecToDouble so a §6.12 shortreal is read as the single-precision value
// its 32 bits hold. Reading them as a double regardless would answer a
// subnormal near zero for every shortreal, which would make a case over one
// pass whatever the simulator stored. It requires a clean elaboration for the
// same reason RunAndGet does.
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

// Lower a design and check variable values.
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
