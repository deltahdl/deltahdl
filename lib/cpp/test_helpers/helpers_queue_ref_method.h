#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

// Creates a bounded queue named `name` of element-width 32 holding `vals`,
// mirroring the manual CreateQueue / push_back / AssignFreshIds sequence used
// by the bounded-queue reference tests.
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

// Registers an automatic void function `func_name(ref v)` whose body invokes
// `q.<method>(method_args)` and then assigns 99 to the reference `v`, then
// calls it passing `q[select_idx]` by reference and evaluates the call. This
// collapses the body-construction + call sequence shared by the QueueRef
// reference tests.
inline void RunQueueRefMethodThenAssign(
    SimFixture& f, std::string_view queue_name, std::string_view method,
    std::vector<Expr*> method_args, uint64_t select_idx,
    std::string_view func_name = "test_fn") {
  RegAutoFunc(f, func_name,
              {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
              {MakeExprStmt(f.arena, MakeMethodCall(f.arena, queue_name, method,
                                                    std::move(method_args))),
               MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, func_name,
                        {MakeSelect(f.arena, queue_name, select_idx)});
  EvalExpr(call, f.ctx, f.arena);
}
