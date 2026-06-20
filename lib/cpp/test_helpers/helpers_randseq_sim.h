#pragma once

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

// Elaborates `src`, lowers and runs it on `f`, then returns the simulation
// variable named `var_name` (or nullptr). The elaborated design is checked
// non-null with a non-fatal expectation so callers can keep their own fatal
// ASSERT on the returned variable and on its value.
inline Variable* RunRandseqAndFindVar(SimFixture& f, const std::string& src,
                                      const char* var_name) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (design == nullptr) {
    return nullptr;
  }
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return f.ctx.FindVariable(var_name);
}
