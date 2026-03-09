#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#include "fixture_simulator.h"

using namespace delta;

inline QueueObject* MakeQueue(SimFixture& f, std::string_view name,
                              const std::vector<uint64_t>& vals) {
  auto* q = f.ctx.CreateQueue(name, 32);
  for (auto v : vals) {
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  }
  q->AssignFreshIds();
  return q;
}

inline void MakeDynArray(SimFixture& f, std::string_view name,
                         const std::vector<uint64_t>& vals) {
  auto* q = f.ctx.CreateQueue(name, 32);
  for (auto v : vals) {
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  }
  ArrayInfo info;
  info.is_dynamic = true;
  info.elem_width = 32;
  info.size = static_cast<uint32_t>(vals.size());
  f.ctx.RegisterArray(name, info);
}

inline void RegAutoFunc(SimFixture& f, std::string_view name,
                        std::vector<FunctionArg> args,
                        std::vector<Stmt*> body) {
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = name;
  func->is_automatic = true;
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = std::move(args);
  func->func_body_stmts = std::move(body);
  f.ctx.RegisterFunction(name, func);
}
