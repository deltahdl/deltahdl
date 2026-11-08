#pragma once

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

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
