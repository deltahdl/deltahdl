#pragma once

#include <cstdint>
#include <fstream>
#include <iterator>
#include <string>
#include <string_view>
#include <vector>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

// Registers an unpacked array `name[lo .. lo+size-1]` of `width`-bit elements,
// each backed by a zero-initialized element variable named `name[index]` (the
// naming convention the simulator uses), so the $readmem* / $writemem* / $fread
// tasks have a memory to operate on. `four_state` selects whether the element
// type is 4-state (the default) or a 2-state type; `descending` declares the
// array address range as descending.
inline void SetupMem(SimFixture& f, const char* name, int lo, int size,
                     uint32_t width, bool four_state = true,
                     bool descending = false) {
  f.ctx.RegisterArray(
      name, {static_cast<uint32_t>(lo), static_cast<uint32_t>(size), width,
             descending, false, false, four_state});
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

// Invokes a $readmem* task on a memory named by a bare identifier, with any
// extra (start/finish) address arguments appended after the memory operand.
inline void Readmem(SimFixture& f, const char* task, const std::string& path,
                    const char* mem, std::vector<Expr*> extra = {}) {
  std::vector<Expr*> args = {MkStr(f.arena, path.c_str()),
                             MakeId(f.arena, mem)};
  for (auto* e : extra) args.push_back(e);
  EvalExpr(MakeSysCall(f.arena, task, args), f.ctx, f.arena);
}

// Invokes a $writemem* task on a memory named by a bare identifier, with any
// extra (start/finish) address arguments appended after the memory operand.
inline void Writemem(SimFixture& f, const char* task, const std::string& path,
                     const char* mem, std::vector<Expr*> extra = {}) {
  std::vector<Expr*> args = {MkStr(f.arena, path.c_str()),
                             MakeId(f.arena, mem)};
  for (auto* e : extra) args.push_back(e);
  EvalExpr(MakeSysCall(f.arena, task, args), f.ctx, f.arena);
}

// Writes `data` to a scratch file `<prefix><tag>.txt` and returns its path.
inline std::string WriteTmp(const char* prefix, const char* tag,
                            const std::string& data) {
  std::string path = std::string(prefix) + tag + ".txt";
  std::ofstream ofs(path);
  ofs << data;
  ofs.close();
  return path;
}

// Reads and returns the entire contents of the file at `path`.
inline std::string ReadFile(const std::string& path) {
  std::ifstream ifs(path);
  return std::string((std::istreambuf_iterator<char>(ifs)),
                     std::istreambuf_iterator<char>());
}
