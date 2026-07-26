#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <initializer_list>
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

// Creates queue `name` initialized with `vals` plus a 32-bit signed variable
// `idx_name` whose value is -1. Returns the queue so callers can build a method
// call that uses MakeId(arena, idx_name) as the (out-of-range/negative) index.
inline QueueObject* MakeQueueWithNegativeIdx(SimFixture& f,
                                             std::string_view name,
                                             const std::vector<uint64_t>& vals,
                                             std::string_view idx_name) {
  auto* q = MakeQueue(f, name, vals);
  auto* idx_var = f.ctx.CreateVariable(idx_name, 32);
  idx_var->value = MakeLogic4Vec(f.arena, 32);
  idx_var->value.words[0].aval = static_cast<uint64_t>(-1);
  idx_var->value.words[0].bval = 0;
  idx_var->value.is_signed = true;
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

// Elaborates and runs `src`, then checks the elements the queue `name` was
// left holding against `expected`, in order.
//
// A queue method is stated as real source and read back as the whole queue,
// since what a method did shows in the ordering and length of what it left
// behind as much as in any single element.
inline void RunAndExpectQueue(const char* src, std::string_view name,
                              std::initializer_list<uint64_t> expected) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue(name);
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), expected.size());
  size_t i = 0;
  for (uint64_t want : expected) {
    EXPECT_EQ(q->elements[i].ToUint64(), want) << i;
    ++i;
  }
}
