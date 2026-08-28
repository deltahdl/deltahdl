#include "elaborator/global_clock_assertion_event.h"

#include <cstddef>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

namespace delta {

bool IsGlobalClockLeadingEvent(const std::vector<EventExpr>& sensitivity) {
  if (sensitivity.size() != 1) return false;
  const Expr* signal = sensitivity.front().signal;
  return signal != nullptr && signal->kind == ExprKind::kSystemCall &&
         signal->callee == "$global_clock";
}

bool SubstituteGlobalClockLeadingEvent(
    std::vector<EventExpr>& sensitivity,
    const std::vector<EventExpr>& global_event) {
  if (global_event.empty()) return false;
  if (!IsGlobalClockLeadingEvent(sensitivity)) return false;
  Expr* gate = sensitivity.front().iff_condition;
  sensitivity = global_event;
  for (auto& ev : sensitivity) {
    if (ev.iff_condition == nullptr) ev.iff_condition = gate;
  }
  return true;
}

namespace {

// One statement of the tree being rewritten, and the statement a rewrite is
// written into. `original` is never written to. `Mutable` returns a copy of
// `original` allocated from `arena`, making it on the first call and returning
// that same copy on every later one, so a statement is copied only once and
// only when something in it or beneath it is actually rewritten. `current` is
// `original` until then, which is what leaves a subtree holding no
// $global_clock event control shared rather than copied.
struct CloneOnWriteStmt {
  const Stmt* original;
  Stmt* current;
  Arena& arena;

  Stmt* Mutable() {
    if (current == original) current = arena.Create<Stmt>(*original);
    return current;
  }
};

// Recurse into every nested statement of the statement `owner` holds, so that
// an event control written anywhere beneath a procedure is reached. §14.14 says
// where $global_clock refers and not where it may be written, so every position
// a statement holds a statement in is one it may be written in.
//
// ForEachChildStmt in elaborator_validate_internal.h states those positions,
// once for the whole elaborator, which is why the list is not written out again
// here. It is walked twice so that the copy stays conditional. The first walk
// rewrites each nested statement of `owner.original` and records what came
// back. The second writes those results into `owner.Mutable()`, and runs only
// where some nested statement was actually rewritten. `owner.Mutable()` is a
// copy of `owner.original` and so has the same fields holding the same nested
// statements, and one function walks both, so the two walks reach the same
// positions in the same order and `next` names the position the result it
// consumes was recorded for.
void SubstituteGlobalClockInSubStmts(
    CloneOnWriteStmt& owner, const std::vector<EventExpr>& global_event) {
  std::vector<Stmt*> rewritten;
  bool any_rewritten = false;
  ForEachChildStmt(owner.original, [&](Stmt* const& sub) {
    Stmt* result =
        SubstituteGlobalClockEventControls(sub, global_event, owner.arena);
    if (result != sub) any_rewritten = true;
    rewritten.push_back(result);
  });
  if (!any_rewritten) return;
  size_t next = 0;
  ForEachChildStmt(owner.Mutable(),
                   [&](Stmt*& slot) { slot = rewritten[next++]; });
}

// §23.6 names a signal from the top of the hierarchy down, one instance name
// per step, and the flattened design the simulator runs keys a declaration on
// that same path with the top-level hierarchy block's own name left off:
// Lowerer::inst_prefix_ in src/simulator/lowerer.h is empty in a top-level
// hierarchy block and gains one instance name per level below it.
// ElaboratorData::current_inst_path_ is the same path with that first
// component kept, so dropping it and its dot is what makes the two agree.
//
// The trailing dot Lowerer::inst_prefix_ carries is left off here, because the
// only two things done with the result are comparing two of them and splitting
// one on its dots.
std::string_view InstancePathBelowTop(std::string_view inst_path) {
  size_t dot = inst_path.find('.');
  if (dot == std::string_view::npos) return {};
  return inst_path.substr(dot + 1);
}

// Expr::text is a non-owning std::string_view, so a name this elaborator
// spells out rather than reading out of the source has to be interned
// somewhere that outlives the design. `at` gives the new identifier the source
// position of the signal it stands for, so a report naming it points at the
// global clocking declaration the name came from.
Expr* MakeIdentifier(std::string_view text, const Expr* at, Arena& arena) {
  auto* id = arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = std::string_view(arena.AllocString(text.data(), text.size()),
                              text.size());
  id->range = at->range;
  return id;
}

// One step of a §23.6 hierarchical name, built the way
// Parser::MakeMemberAccess in src/parser/expr_parser.cpp builds it, so a name
// written here has the same shape as one the parser read out of the source.
Expr* MakeMemberAccess(Expr* base, std::string_view member, const Expr* at,
                       Arena& arena) {
  auto* acc = arena.Create<Expr>();
  acc->kind = ExprKind::kMemberAccess;
  acc->lhs = base;
  acc->rhs = MakeIdentifier(member, at, arena);
  acc->range = base->range;
  return acc;
}

// §23.6 gives `$root` as the first component of a name written from the top of
// the instantiated design: "The instance name $root refers to the top of the
// instantiated design and is used to unambiguously gain access to the top of
// the design." A string literal has static storage duration, so unlike a name
// spelled out of an instance path it needs no copy in the arena.
constexpr std::string_view kRootScope = "$root";

// `signal` re-allocated as a name absolute from the top of the instantiated
// design, carrying `$root` in Expr::scope_prefix the way
// Parser::MakeSysScopePrefix in src/parser/expr_parser_calls.cpp carries it for
// a `$root.clk` written in a source.
//
// No instance name stands between the `$root` and the signal, because the
// flattened design the simulator runs keys a top-level hierarchy block's own
// declarations under no instance prefix at all: see InstancePathBelowTop
// above, whose result is empty for exactly that block.
//
// A new Expr is allocated rather than the prefix written onto `signal`. The
// declared event expression belongs to the ModuleDecl the global clocking was
// written in, and every instance of every module below it reads that one node,
// so writing to it would qualify the declaring scope's own references too.
Expr* RootQualifySignal(const Expr* signal, Arena& arena) {
  Expr* id = MakeIdentifier(signal->text, signal, arena);
  id->scope_prefix = kRootScope;
  return id;
}

// `signal` prefixed by the instance names in `prefix`, so that the identifier
// `clk` under a `prefix` of "sub1.inner" becomes `sub1.inner.clk`. An empty
// `prefix` names no instance to reach through and returns `signal` itself.
Expr* QualifySignal(Expr* signal, std::string_view prefix, Arena& arena) {
  Expr* base = nullptr;
  size_t pos = 0;
  while (pos < prefix.size()) {
    size_t dot = prefix.find('.', pos);
    size_t end = dot == std::string_view::npos ? prefix.size() : dot;
    std::string_view component = prefix.substr(pos, end - pos);
    base = base == nullptr ? MakeIdentifier(component, signal, arena)
                           : MakeMemberAccess(base, component, signal, arena);
    pos = end + 1;
  }
  if (base == nullptr) return signal;
  return MakeMemberAccess(base, signal->text, signal, arena);
}

}  // namespace

const std::vector<EventExpr>* EffectiveGlobalClockingEvent(
    const std::vector<EventExpr>* declared_events,
    std::string_view declaring_inst_path,
    std::string_view referencing_inst_path, Arena& arena) {
  if (declared_events == nullptr) return nullptr;
  std::string_view declaring = InstancePathBelowTop(declaring_inst_path);
  std::string_view referencing = InstancePathBelowTop(referencing_inst_path);
  // §14.14 rule a): the declaration is in the scope holding the reference, so
  // its event expression names signals of that scope and stands as written.
  if (declaring == referencing) return declared_events;
  auto* qualified = arena.Create<std::vector<EventExpr>>(*declared_events);
  for (auto& ev : *qualified) {
    if (ev.signal == nullptr) continue;
    // §23.6 spells a hierarchical name out of identifiers, and only a plain
    // identifier is one. An event whose signal is any other expression is left
    // as it stands, because CollectExprIdentifiers in src/simulator/awaiters.h
    // has no ExprKind::kMemberAccess case: on the compound path it would
    // descend into a qualified name and hand back its two components as two
    // bare signal names, neither of which names anything in the referencing
    // instance. EventExpr::iff_condition is left alone for the same reason,
    // being an arbitrary expression rather than a name.
    if (ev.signal->kind != ExprKind::kIdentifier) continue;
    // An empty `declaring` is the declaration in the top-level hierarchy
    // block, which is not an instance and so has no instance name to reach it
    // through. §23.6 names it from the top of the instantiated design instead.
    ev.signal = declaring.empty() ? RootQualifySignal(ev.signal, arena)
                                  : QualifySignal(ev.signal, declaring, arena);
  }
  return qualified;
}

Stmt* SubstituteGlobalClockEventControls(
    Stmt* stmt, const std::vector<EventExpr>& global_event, Arena& arena) {
  // An empty `global_event` substitutes nothing, so the whole walk is skipped
  // rather than run to no effect: §14.14 reports a $global_clock reference with
  // no global clocking declaration in scope, and this leaves that report the
  // only account of it.
  if (stmt == nullptr || global_event.empty()) return stmt;
  CloneOnWriteStmt owner{stmt, stmt, arena};
  if (IsGlobalClockLeadingEvent(stmt->events)) {
    SubstituteGlobalClockLeadingEvent(owner.Mutable()->events, global_event);
  }
  SubstituteGlobalClockInSubStmts(owner, global_event);
  return owner.current;
}

}  // namespace delta
