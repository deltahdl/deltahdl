#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

inline std::vector<uint64_t> RunSeededAndRead(
    const std::string& src, std::initializer_list<const char*> names) {
  SimFixtureSeeded f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (design == nullptr) {
    return std::vector<uint64_t>(names.size(), 0);
  }
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  std::vector<uint64_t> out;
  out.reserve(names.size());
  for (const char* name : names) {
    out.push_back(f.ctx.FindVariable(name)->value.ToUint64());
  }
  return out;
}
