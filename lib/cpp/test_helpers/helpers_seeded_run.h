#pragma once

#include <cstdint>
#include <initializer_list>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

// Elaborate, lower, and run `src` in a freshly constructed seeded simulation
// context, then read back each named scalar variable as an unsigned value. The
// random-stability tests replay the same fork program from a fixed
// initialization seed and compare the per-variable draws, so they share this
// elaborate/lower/run/read sequence and differ only in the source text and the
// set of variables they inspect.
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
