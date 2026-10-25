#pragma once

#include <cstddef>
#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
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

// §16.8.2 with §16.10: the declaration of the local variable the local
// variable formal argument `index` of `decl` is, under the formal's name and
// of the type the formal is declared with: its type keyword, with its
// signing, the keyword's own or the one written after it (§6.11.3), or the
// type name written in its place, and the packed dimensions (§7.4.1) written
// after either.
SeqLocalDecl LocalFormalDecl(const ModuleItem& decl, size_t index);

// §16.10 with §6.18 and §7.4.1: the data type the local `decl` is declared
// with: the type name written in its keyword's place, of kind kImplicit where
// a keyword is written, with the packed dimensions written after either.
DataType LocalDataType(const SeqLocalDecl& decl);

// §16.10: the local `decl` stood up as a variable of the innermost scope
// holding `value`, of its declared type's state and signedness, with the
// packed dimensions it was declared with, which a select of it resolves
// against (§7.4.1), and the layout of the packed structure its type name
// stands for, which a member select of it reads through (§7.2). Both are
// kept on the variable, so they end with the scope, as a pattern
// identifier's layout does.
Variable* StandUpLocal(const SeqLocalDecl& decl, const Logic4Vec& value,
                       SimContext& ctx);

// §16.10 with §6.8: the local `decl` stood up as StandUpLocal stands it up,
// holding the value it holds before any assignment, x for a 4-state type and
// 0 for a 2-state one, at its declared width.
Variable* StandUpUnassignedLocal(const SeqLocalDecl& decl, SimContext& ctx,
                                 Arena& arena);

// §16.10 with §6.11.2: `value` assigned whole to the local `var`, at its
// width and signedness, the x and z bits of a 4-state value turned to 0 in a
// 2-state local.
void AssignWholeLocal(Variable& var, const Logic4Vec& value, Arena& arena);

// §16.10: `rhs` assigned with the operator of the match item `item` to the
// local `local`, which stands in scope under the name the item gives it:
// whole, as AssignWholeLocal assigns it, or, with A.10 footnote 51,
// through the item's target, which selects within the local or names a
// member of it, as an assignment's target is written. The local takes words
// of its own first, since an attempt's copy may share them with another's.
void AssignMatchItem(const SeqMatchAssign& item, Logic4Vec rhs, Variable& local,
                     SimContext& ctx, Arena& arena);

// §16.10: the values a new attempt's copies of the locals `decls` begin with.
std::vector<Logic4Vec> InitialLocals(const std::vector<SeqLocalDecl>& decls,
                                     SimContext& ctx, Arena& arena);

// §16.11: schedules a subroutine call attached to a sequence for the match
// being read now.
void ScheduleMatchCall(const Expr* call, SimContext& ctx, Arena& arena);

}  // namespace delta
