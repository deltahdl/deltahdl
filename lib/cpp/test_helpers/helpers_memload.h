#pragma once

#include <cstdint>
#include <fstream>
#include <iterator>
#include <string>
#include <string_view>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

// Registers an unpacked array `name[lo .. lo+size-1]` of `width`-bit 4-state
// elements, each backed by a zero-initialized element variable named
// `name[index]` (the naming convention the simulator uses), so the $readmem* /
// $writemem* / $fread tasks have a memory to operate on. The address range
// ascends. A test wanting a 2-state element type or a descending range states
// the ArrayInfo itself and calls SimContext::RegisterArray.
inline void SetupMem(SimFixture& f, const char* name, int lo, int size,
                     uint32_t width) {
  f.ctx.RegisterArray(
      name, {static_cast<uint32_t>(lo), static_cast<uint32_t>(size), width,
             false, false, false, true});
  for (int i = 0; i < size; ++i) {
    std::string nm = std::string(name) + "[" + std::to_string(lo + i) + "]";
    auto* s = f.arena.AllocString(nm.c_str(), nm.size());
    auto* v = f.ctx.CreateVariable(std::string_view(s, nm.size()), width);
    v->value = MakeLogic4VecVal(f.arena, width, 0);
  }
}

// Returns the element variable `name[addr]` of an array registered by SetupMem.
inline Variable* Cell(SimFixture& f, const char* name, int addr) {
  std::string nm = std::string(name) + "[" + std::to_string(addr) + "]";
  return f.ctx.FindVariable(nm);
}

// Reads and returns the entire contents of the file at `path`.
inline std::string ReadFile(const std::string& path) {
  std::ifstream ifs(path);
  return std::string((std::istreambuf_iterator<char>(ifs)),
                     std::istreambuf_iterator<char>());
}
