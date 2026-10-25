#pragma once

#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/expr_substitute.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

// §16.10 and §6.11: the width of a local declared with a data type keyword,
// 1 for a bit type.
uint32_t LocalWidth(TokenKind type_kw);

// §16.10 with §6.18 and §7.4.1: the width of the local `decl`: the width
// the type name it is declared with stands for, or a bit where a keyword is
// written, times the product of the packed dimensions' spans written after
// it, each bound read at the run; its keyword's width where neither a name
// nor a dimension is written.
uint32_t LocalWidth(const SeqLocalDecl& decl, SimContext& ctx, Arena& arena);

// §16.10 and §6.8: the state of a local declared with a data type keyword,
// and the value it holds before any assignment, x for a 4-state type and 0
// for a 2-state one.
bool LocalIs4State(TokenKind type_kw);

// §6.11, Table 6-8: whether a local declared with a data type keyword is
// signed, as the integer atom types other than time are and time and the
// vector types bit, logic and reg are not.
bool LocalIsSigned(TokenKind type_kw);

// §6.18: whether the local `decl` is of a 4-state type, the type its type
// name stands for or its keyword.
bool LocalIs4State(const SeqLocalDecl& decl, const SimContext& ctx);

// §6.11 and §6.18: whether the local `decl` is signed, as its signing keyword
// writes where it writes one and otherwise as the type its type name stands
// for or its keyword is.
bool LocalIsSigned(const SeqLocalDecl& decl, const SimContext& ctx);

// §16.10: the local `decl` stood up as a variable of the innermost scope
// holding `value`, of its declared type's state and signedness, with the
// packed dimensions it was declared with, which a select of it resolves
// against (§7.4.1), and the layout of the packed structure its type name
// stands for, which a member select of it reads through (§7.2). Both are
// kept on the variable, so they end with the scope, as a pattern
// identifier's layout does.
Variable* StandUpLocal(const SeqLocalDecl& decl, const Logic4Vec& value,
                       SimContext& ctx);

// §16.10 with A.10 footnote 51: `rhs` assigned with the operator of `item`
// to its target, which selects within `local` or names a member of it, as
// an assignment's target is written, `local` standing in scope for the local
// the target names. The local takes words of its own first, since an
// attempt's copy may share them with another's.
void AssignMatchItemTarget(const SeqMatchAssign& item, Logic4Vec rhs,
                           Variable& local, SimContext& ctx, Arena& arena);

// §16.10: the value a local holding `whole` takes when the match item `item`
// assigns it `rhs` with its operator, in words of its own and at its width:
// the whole local, or what the item's target selects within it, written
// through a variable standing for the local under the name `lvar` gives it,
// in a scope of its own (AssignMatchItemTarget).
Logic4Vec AssignedLocalValue(const SeqMatchAssign& item, const Logic4Vec& whole,
                             Logic4Vec rhs, SimContext& ctx, Arena& arena);

// §16.10 with A.10 footnote 51: the target of `item`, where it has one, with
// `actuals` in place of the formals it reads. Its local is renamed with
// `item` where an actual names the local it is bound to, and kept where
// `keeps_local` says the local stands as the literal of an attempt's copy,
// which AssignedLocalValue writes through by the local's own name.
Expr* SubstituteTarget(const SeqMatchAssign& item, bool keeps_local,
                       const ActualsByFormal& actuals, Arena& arena);

// §16.10: the values a new attempt's copies of the locals `decls` begin with.
std::vector<Logic4Vec> InitialLocals(const std::vector<SeqLocalDecl>& decls,
                                     SimContext& ctx, Arena& arena);

// §16.11: schedules a subroutine call attached to a sequence for the match
// being read now.
void ScheduleMatchCall(const Expr* call, SimContext& ctx, Arena& arena);

}  // namespace delta
