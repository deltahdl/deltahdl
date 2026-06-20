#pragma once

#include <cstdint>
#include <string_view>
#include <utility>
#include <vector>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

// Drive a stochastic-analysis queue task/function (§20.15) through the
// evaluator and report the value left in its trailing `status` output argument.
// §20.15.6 requires every queue management task and function to return such an
// output status code.
inline uint64_t RunQueueCall(SimFixture& f, std::string_view name,
                             std::vector<Expr*> args,
                             std::string_view status_name) {
  auto* call = MkSysCall(f.arena, name, std::move(args));
  EvalExpr(call, f.ctx, f.arena);
  return f.ctx.FindVariable(status_name)->value.ToUint64();
}

// $q_initialize(q_id, q_type, max_length, status): create a queue with the
// given type/length, returning the creation status. Pre-seeds a fresh `status`
// variable each time.
inline uint64_t QInitialize(SimFixture& f, uint64_t q_id, int64_t q_type,
                            int64_t max_length) {
  MakeVar(f, "st", 32, 0xDEAD);
  return RunQueueCall(
      f, "$q_initialize",
      {MkInt(f.arena, q_id), MkInt(f.arena, static_cast<uint64_t>(q_type)),
       MkInt(f.arena, static_cast<uint64_t>(max_length)), MkId(f.arena, "st")},
      "st");
}

// $q_add(q_id, job_id, inform_id, status): place an entry carrying the given
// job_id and inform_id onto queue q_id, returning the reported status.
inline uint64_t QAdd(SimFixture& f, uint64_t q_id, uint64_t job_id = 1,
                     uint64_t inform_id = 0) {
  MakeVar(f, "st", 32, 0xDEAD);
  return RunQueueCall(f, "$q_add",
                      {MkInt(f.arena, q_id), MkInt(f.arena, job_id),
                       MkInt(f.arena, inform_id), MkId(f.arena, "st")},
                      "st");
}

// $q_remove(q_id, job_id, inform_id, status): take one entry off queue q_id,
// routing the removed job_id/inform_id to throwaway variables; only the
// reported status is returned.
inline uint64_t QRemoveStatus(SimFixture& f, uint64_t q_id) {
  MakeVar(f, "st", 32, 0xDEAD);
  MakeVar(f, "job", 32, 0);
  MakeVar(f, "inf", 32, 0);
  return RunQueueCall(f, "$q_remove",
                      {MkInt(f.arena, q_id), MkId(f.arena, "job"),
                       MkId(f.arena, "inf"), MkId(f.arena, "st")},
                      "st");
}

// $q_remove(q_id, job_id, inform_id, status): remove one entry from queue q_id.
// The job_id and inform_id are routed to caller-named variables so the outputs
// can be inspected; the call returns the reported status.
inline uint64_t QRemoveInto(SimFixture& f, uint64_t q_id,
                            std::string_view job_var,
                            std::string_view inform_var) {
  MakeVar(f, "st", 32, 0xDEAD);
  MakeVar(f, job_var, 32, 0xBEEF);
  MakeVar(f, inform_var, 32, 0xBEEF);
  return RunQueueCall(f, "$q_remove",
                      {MkInt(f.arena, q_id), MkId(f.arena, job_var),
                       MkId(f.arena, inform_var), MkId(f.arena, "st")},
                      "st");
}

// $q_full(q_id, status): evaluate the function and return its 0/1 fullness
// result. The status output is routed to a caller-named variable so it can be
// inspected separately when needed.
inline uint64_t QFullValue(SimFixture& f, uint64_t q_id,
                           std::string_view status_var) {
  MakeVar(f, status_var, 32, 0xDEAD);
  auto* call = MkSysCall(f.arena, "$q_full",
                         {MkInt(f.arena, q_id), MkId(f.arena, status_var)});
  return EvalExpr(call, f.ctx, f.arena).ToUint64();
}

// Read back the unsigned value currently held by a simulator variable.
inline uint64_t ReadQueueVar(SimFixture& f, std::string_view name) {
  return f.ctx.FindVariable(name)->value.ToUint64();
}
