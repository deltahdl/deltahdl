#pragma once

#include <cstdint>
#include <string_view>
#include <utility>
#include <vector>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"

using namespace delta;

inline QueueObject* MakeBoundedQueue(SimFixture& f, std::string_view name,
                                     int32_t bound,
                                     const std::vector<uint64_t>& vals) {
  auto* q = f.ctx.CreateQueue(name, 32, bound);
  for (auto v : vals) {
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  }
  q->AssignFreshIds();
  return q;
}

inline void RunQueueRefMethodThenAssign(SimFixture& f,
                                        std::string_view queue_name,
                                        std::string_view method,
                                        std::vector<Expr*> method_args,
                                        uint64_t select_idx) {
  constexpr std::string_view kFuncName = "test_fn";
  RegAutoFunc(f, kFuncName,
              {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
              {MakeExprStmt(f.arena, MakeMethodCall(f.arena, queue_name, method,
                                                    std::move(method_args))),
               MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, kFuncName,
                        {MakeSelect(f.arena, queue_name, select_idx)});
  EvalExpr(call, f.ctx, f.arena);
}
