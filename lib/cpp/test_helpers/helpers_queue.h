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

inline void MakeDynArray(SimFixture& f, std::string_view name,
                         const std::vector<uint64_t>& vals) {
  auto* q = f.ctx.CreateQueue(name, 32);
  for (auto v : vals) {
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  }
  // A dynamic array's elements carry ids exactly as a queue's do, and the two
  // lists are indexed together: Lowerer::LowerDynArrayInit and the `new[]` arm
  // beside it both call AssignFreshIds, so a dynamic array a run built always
  // has one id per element. Leaving them empty here built a shape no run
  // produces, and a reference taken on an element of such an array was
  // recorded against no identity at all.
  q->AssignFreshIds();
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
