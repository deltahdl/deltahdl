#include <cstdint>
#include <utility>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir_scopes.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

void Lowerer::InstallGenBlockConsts(const GenBlockConsts& consts, Process* p) {
  if (consts.empty()) return;
  Scope scope;
  for (const auto& [name, value] : consts) {
    auto* var = arena_.Create<Variable>();
    var->value = MakeLogic4VecVal(arena_, 32, static_cast<uint64_t>(value));
    var->value.is_signed = true;
    var->is_signed = true;
    scope.vars[name] = var;
  }
  p->saved_scope_stack.push_back(std::move(scope));
}

}  // namespace delta
