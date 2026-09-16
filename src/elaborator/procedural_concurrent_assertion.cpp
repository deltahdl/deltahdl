#include "elaborator/procedural_concurrent_assertion.h"

#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/property_instance.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "parser/ast.h"
#include "parser/expr_substitute.h"

namespace delta {

namespace {

bool IsProceduralConcurrent(const Stmt* s) {
  return s != nullptr && s->is_procedural_concurrent &&
         (s->kind == StmtKind::kAssertImmediate ||
          s->kind == StmtKind::kAssumeImmediate ||
          s->kind == StmtKind::kCoverImmediate);
}

bool IsAssertionStatement(const Stmt* s) {
  return s->kind == StmtKind::kAssertImmediate ||
         s->kind == StmtKind::kAssumeImmediate ||
         s->kind == StmtKind::kCoverImmediate;
}

// The procedural concurrent assertions of the procedure in source order,
// those in the action block of another among them.
void CollectProceduralAssertions(Stmt* s, std::vector<Stmt*>& out) {
  if (s == nullptr) return;
  if (IsProceduralConcurrent(s)) out.push_back(s);
  ForEachChildStmt(
      s, [&out](Stmt* const& sub) { CollectProceduralAssertions(sub, out); });
}

// §16.14.6's requirements (a) and (b) read off the procedure: whether it
// holds a blocking timing control, a delay or a wait, and the event
// controls its body holds, which stand beside the one an always procedure
// opens with.
struct ProcedureTiming {
  bool blocking = false;
  std::vector<const Stmt*> event_controls;
};

void ScanTiming(const Stmt* s, ProcedureTiming& timing) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kDelay || s->kind == StmtKind::kWait ||
      s->kind == StmtKind::kWaitOrder || s->kind == StmtKind::kWaitFork) {
    timing.blocking = true;
  }
  if (s->kind == StmtKind::kEventControl) timing.event_controls.push_back(s);
  ForEachChildStmt(s, [&timing](Stmt* const& sub) { ScanTiming(sub, timing); });
}

// §16.14.6 (c)(2): the names the procedure references other than as a
// clocking event or within an assertion statement, the operands of each
// statement's expressions and the targets it writes; an event control's
// events are clocking events and an assertion statement is skipped whole,
// its action block with it.
void CollectReferences(const Stmt* s, std::unordered_set<std::string>& out) {
  if (s == nullptr || IsAssertionStatement(s)) return;
  const Expr* exprs[] = {s->condition, s->lhs,      s->rhs,   s->for_cond,
                         s->expr,      s->var_init, s->delay, s->cycle_delay};
  for (const Expr* e : exprs) CollectExprReads(e, out);
  for (const auto& ci : s->case_items) {
    for (const Expr* pat : ci.patterns) CollectExprReads(pat, out);
  }
  for (const auto& rc : s->randcase_items) CollectExprReads(rc.first, out);
  ForEachChildStmt(s,
                   [&out](Stmt* const& sub) { CollectReferences(sub, out); });
}

// Whether `name` is an event variable or a clocking block of `mod`, the
// two things §16.14.6 (c)(1) lets an event expression consist solely of
// without an edge.
bool NamesEventOrClockingBlock(std::string_view name, const RtlirModule* mod) {
  if (mod == nullptr) return false;
  for (const ModuleItem* block : mod->clocking_blocks) {
    if (block->name == name) return true;
  }
  for (const RtlirVariable& var : mod->variables) {
    if (var.name == name && var.is_event) return true;
  }
  return false;
}

// §16.14.6 (c): whether `ev` is an event expression the clock can be
// inferred from: solely an event variable or a clocking block identifier,
// or an edge over an expression, with an iff or without, and in either
// case naming nothing the procedure references elsewhere.
bool QualifiesAsClock(const EventExpr& ev, const RtlirModule* mod,
                      const std::unordered_set<std::string>& references) {
  if (ev.signal == nullptr || ev.is_sequence_event) return false;
  if (ev.edge == Edge::kNone) {
    if (ev.signal->kind != ExprKind::kIdentifier ||
        !NamesEventOrClockingBlock(ev.signal->text, mod)) {
      return false;
    }
  }
  std::unordered_set<std::string> terms;
  CollectExprReads(ev.signal, terms);
  for (const std::string& term : terms) {
    if (references.count(term) != 0) return false;
  }
  return true;
}

// §16.14.6: the clock the procedure gives an assertion embedded in it that
// opens with none, or an empty list where the requirements fail.
std::vector<EventExpr> InferredProcedureClock(const ModuleItem* procedure,
                                              const RtlirModule* mod) {
  ProcedureTiming timing;
  ScanTiming(procedure->body, timing);
  if (timing.blocking) return {};
  // (b): exactly one event control, the always procedure's own or one the
  // body holds; an always_comb or always_latch infers its sensitivity and
  // holds none, and an implicit `@*` names no clock.
  const std::vector<EventExpr>* events = nullptr;
  if (!procedure->sensitivity.empty() && !procedure->is_star_sensitivity) {
    if (!timing.event_controls.empty()) return {};
    events = &procedure->sensitivity;
  } else if (timing.event_controls.size() == 1 &&
             !timing.event_controls[0]->is_star_event) {
    events = &timing.event_controls[0]->events;
  } else {
    return {};
  }
  // (c): one and only one of its event expressions qualifies.
  std::unordered_set<std::string> references;
  CollectReferences(procedure->body, references);
  std::vector<EventExpr> clock;
  for (const EventExpr& ev : *events) {
    if (QualifiesAsClock(ev, mod, references)) clock.push_back(ev);
  }
  if (clock.size() != 1) return {};
  return clock;
}

// Whether the body of `decl` is one the run reads; a statement instantiating
// a property whose body was not captured is reported unevaluated, as a
// static one is, and left as no concurrent assertion.
bool BodyIsRead(Stmt* stmt, const ModuleItem* decl, DiagEngine& diag) {
  if (decl->prop_body_expr != nullptr || decl->prop_body_tree != nullptr) {
    return true;
  }
  diag.Warning(stmt->range.start,
               "procedural concurrent assertion is not evaluated: the body of "
               "property \"" +
                   std::string(decl->name) +
                   "\" is not a form this tool evaluates",
               Subclause("16.14.6"));
  stmt->is_concurrent_clocked = false;
  return false;
}

// §16.12.1 and §16.13.4, for a statement in procedural code: the body of
// the named property or sequence the spec instantiates, as
// SubstitutePropertyInstance and SubstituteSequenceInstance give a static
// statement's, the property's boolean body with the actuals in the
// formals' places, any other body as a tree whose root is the instance for
// the run to expand, and a sequence as a sequence declaration of one
// operand; the declaration's clock, or the one flowing into it, is the
// statement's where the spec opened with none.
void SubstituteInstance(Stmt* stmt, const PropertyRegistry& registry,
                        const InferredAtInstance& inferred, Arena& arena,
                        DiagEngine& diag) {
  if (stmt->assert_property != nullptr || stmt->assert_sequence != nullptr) {
    return;
  }
  Expr* instance = stmt->assert_expr;
  const ModuleItem* seq =
      InstantiatedDecl(instance, ModuleItemKind::kSequenceDecl, registry);
  // §16.14.7: the inferred functions among the defaults are replaced by
  // what is inferred at the statement, the clock its spec opens with, the
  // procedure's or the default clocking's.
  InferredAtInstance here = inferred;
  if (!stmt->assert_clock.empty()) here.clock = stmt->assert_clock;
  FillInferredDefaults(
      instance,
      seq != nullptr
          ? seq
          : InstantiatedDecl(instance, ModuleItemKind::kPropertyDecl, registry),
      here, arena);
  if (seq != nullptr) {
    stmt->assert_property = arena.Create<PropertyExprNode>();
    stmt->assert_property->kind = PropertyExprNode::Kind::kSequence;
    stmt->assert_property->sequence = SequenceInstanceBody(instance, arena);
    if (stmt->assert_clock.empty()) stmt->assert_clock = seq->seq_clock;
    return;
  }
  const ModuleItem* decl =
      InstantiatedDecl(instance, ModuleItemKind::kPropertyDecl, registry);
  if (decl == nullptr || !BodyIsRead(stmt, decl, diag)) return;
  ActualsByFormal actuals = BindActuals(decl->prop_formals, instance);
  if (decl->prop_body_expr != nullptr && !InstanceHasTreeActual(instance)) {
    stmt->assert_expr = SubstituteFormals(decl->prop_body_expr, actuals, arena);
    stmt->assert_negated = decl->prop_negated;
  } else {
    stmt->assert_property = arena.Create<PropertyExprNode>();
    stmt->assert_property->boolean = instance;
  }
  if (stmt->assert_disable_iff == nullptr) {
    stmt->assert_disable_iff =
        SubstituteFormals(decl->prop_disable_iff, actuals, arena);
  }
  if (!stmt->assert_clock.empty()) return;
  const std::vector<EventExpr>& clock = decl->prop_clock.empty()
                                            ? FlowedBodyClock(decl, registry)
                                            : decl->prop_clock;
  for (const EventExpr& ev : clock) {
    stmt->assert_clock.push_back(SubstituteClockEvent(ev, actuals, arena));
  }
}

}  // namespace

void ElaborateProceduralConcurrentAssertions(ModuleItem* procedure,
                                             const RtlirModule* mod,
                                             const PropertyRegistry& registry,
                                             Arena& arena, DiagEngine& diag) {
  std::vector<Stmt*> assertions;
  CollectProceduralAssertions(procedure->body, assertions);
  if (assertions.empty()) return;
  std::vector<EventExpr> inferred = InferredProcedureClock(procedure, mod);
  std::vector<EventExpr> fallback = DefaultClockingEvent(mod);
  InferredAtInstance at_instance;
  at_instance.clock = inferred.empty() ? fallback : inferred;
  at_instance.disable = mod != nullptr ? mod->default_disable_iff : nullptr;
  for (Stmt* stmt : assertions) {
    if (!stmt->is_concurrent_clocked) continue;
    SubstituteInstance(stmt, registry, at_instance, arena, diag);
    if (!stmt->is_concurrent_clocked) continue;
    PromoteSequenceInstances(stmt->assert_property, registry, arena);
    if (stmt->assert_clock.empty()) stmt->assert_clock = inferred;
    if (stmt->assert_clock.empty()) stmt->assert_clock = fallback;
    if (!stmt->assert_clock.empty()) continue;
    diag.Error(stmt->range.start,
               "no clock is inferred for the procedural concurrent assertion: "
               "its property_spec opens with no clocking event, the procedure "
               "gives it none, holding a blocking timing control, more or "
               "fewer event controls than one or no unique event expression "
               "of the form the clause names, and the scope has no default "
               "clocking",
               Subclause("16.14.6"));
  }
}

}  // namespace delta
