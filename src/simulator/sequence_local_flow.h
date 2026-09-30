#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_name_tables.h"

namespace delta {

// §16.10: whether `name` is an entire actual of `instance`, the only way a
// local may be passed to an instance to which `triggered` is applied.
bool PassedAsWholeActual(const Expr* instance, std::string_view name);

// §16.10: the locals of each attempt of a monitored sequence that matched,
// `ended`, each value paired with the name `locals` declares it under, in the
// order of the flattened body's locals.
std::vector<DeclaredNameTables::MatchLocals> NamedMatchLocals(
    const std::vector<SeqLocalDecl>& locals,
    const std::vector<std::vector<Logic4Vec>>& ended);

// §16.10: the matches an operand that is `triggered` applied to an instance,
// the whole Boolean, hands locals on from: those of the instance's monitor
// that ended at this time step; null for any other operand.
const std::vector<DeclaredNameTables::MatchLocals>* FlowedMatches(
    const Expr* operand, SimContext& ctx);

// §16.10: a local passed as an entire actual to the instance flows out of
// `triggered` applied to it with the value match `pick` assigned it, taken
// into the local of that name the reading attempt stands up.
void TakeFlowedLocals(const Expr* operand, uint32_t pick, SimContext& ctx,
                      Arena& arena);

}  // namespace delta
