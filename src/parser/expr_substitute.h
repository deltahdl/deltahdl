#pragma once

#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

namespace delta {

// An expression to stand for each name, the actual argument bound to a formal
// in §16.8's and §16.12's instantiation of a named sequence or property.
using ActualsByFormal = std::unordered_map<std::string_view, Expr*>;

// §F.4.1's rewriting: a copy of `e` in which every identifier the map names
// is replaced by the expression mapped to it, the rest copied node by node;
// nullptr for nullptr. The copy shares nothing with `e` but the leaves the
// map supplies.
Expr* SubstituteFormals(const Expr* e, const ActualsByFormal& actuals,
                        Arena& arena);

// §16.8 and §16.12: the actuals of `instance`, written as a call, bound to
// `formals`, by position for the leading actuals and by name for the
// `.formal(actual)` ones; empty for an instance written as a name alone.
ActualsByFormal BindActuals(const std::vector<std::string_view>& formals,
                            const Expr* instance);

// §16.8: the actuals BindActuals binds, and each formal the instance leaves
// with none, or with an empty one, bound to its default actual argument where
// `defaults`, parallel to `formals`, declares one.
ActualsByFormal BindActualsWithDefaults(
    const std::vector<std::string_view>& formals,
    const std::vector<Expr*>& defaults, const Expr* instance);

// §9.4.2: the event `ev` as an event expression given as an actual argument
// is kept: an edge keyword over its signal opening at `loc`, or the signal
// alone where the event names no edge, under an `iff` holding its guard where
// it has one.
Expr* EventAsActual(const EventExpr& ev, SourceLoc loc, Arena& arena);

// §9.4.2: the event expressions `lhs` and `rhs` joined by `or`.
Expr* EitherEventActual(Expr* lhs, Expr* rhs, Arena& arena);

// §16.8.1 b) and §9.4.2: whether `actual` is an event expression given to a
// formal of type event as the parser keeps one: an edge keyword over its
// signal, an `iff` over an event and its guard, or an `or` of two events.
bool IsEventActual(const Expr* actual);

// §9.4.2: the events the event expression `actual` joins by `or`, each with
// its edge, none where no edge keyword is written, its signal and its guard.
std::vector<EventExpr> EventsOfActual(Expr* actual);

// §16.8.1 b) and §9.4.2: the events a clock event `ev` stands for where the
// formal it names is bound to the event expression `actual`, appended to
// `out`: one for each event of the actual, with that event's edge and signal,
// guarded where `ev`'s own guard and the event's both hold. `ev`'s guard is
// taken as it is, its formals already substituted.
void AppendActualEvents(const EventExpr& ev, Expr* actual, Arena& arena,
                        std::vector<EventExpr>& out);

// §16.8 and §16.12: the name an instance of a named sequence or property is
// declared or registered under: its bare name, written as an identifier or
// called; "pk::name" where it is written through a package scope, `pk::s` or
// `pk::p(a, b)` (§26.3); and "u.name" where it is written through an interface
// instance, `u.s` (§23.6). Empty for any other expression.
std::string InstanceDeclName(const Expr* instance);

// §23.6: whether two expressions name the same object by the same spelling:
// an identifier by its text and scope prefix, a member access, `i0.clk`, whose
// own text is empty, by the whole path, and a select of a constant index by
// its base and index; any other expression of the same kind by its text.
bool SamePath(const Expr* a, const Expr* b);

}  // namespace delta
