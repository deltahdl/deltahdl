#include "simulator/deferred_caller.h"

#include <memory>

#include "simulator/process.h"
#include "simulator/sim_context.h"

namespace delta {

std::shared_ptr<Process> SnapshotCallingProcess(SimContext& ctx) {
  Process* proc = ctx.CurrentProcess();
  if (proc == nullptr) return nullptr;
  auto snap = std::make_shared<Process>();
  snap->stand_in = true;
  snap->kind = proc->kind;
  snap->inst_prefix = proc->inst_prefix;
  snap->gen_prefixes = proc->gen_prefixes;
  snap->gen_block_name = proc->gen_block_name;
  snap->saved_named_scopes = ctx.ActiveNamedScopes();
  ctx.CopyCarriedStacksTo(*snap);
  return snap;
}

CallerStandIn::CallerStandIn(Process* caller, SimContext& ctx)
    : ctx_(ctx), displaced_(ctx.CurrentProcess()) {
  ctx_.SetCurrentProcess(caller);
}

CallerStandIn::~CallerStandIn() { ctx_.SetCurrentProcess(displaced_); }

}  // namespace delta
