#include <string_view>
#include <utility>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

// §27.4: gives the thread the implicit localparam of each loop generate block
// it was elaborated inside -- an integer parameter named after the loop index,
// holding the value that index had for this instance. Every unrolled instance
// runs the same body, so the value cannot be found by name in the shared design
// and has to be private to the thread. Parking it in the thread's own scope
// stack does that: SimContext swaps that stack in whenever this thread runs,
// and FindVariable consults it before the design-wide names, so `i` reads this
// instance's index while everything else still resolves as usual.
void Lowerer::InstallGenBlockConsts(const GenBlockConsts& consts, Process* p) {
  if (consts.empty()) return;
  Scope scope;
  for (const auto& [name, value] : consts) {
    auto* var = arena_.Create<Variable>();
    // A genvar is an integer (§27.4), so the parameter it names is 32-bit
    // signed -- which is what makes a negative loop index compare as negative.
    var->value = MakeLogic4VecVal(arena_, 32, static_cast<uint64_t>(value));
    var->value.is_signed = true;
    var->is_signed = true;
    scope.vars[name] = var;
  }
  p->saved_scope_stack.push_back(std::move(scope));
}

}  // namespace delta
