#include "elaborator/procedural_concurrent_assertion.h"

#include <algorithm>
#include <array>
#include <format>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/property_instance.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/semantic_leading_clocks.h"
#include "elaborator/sensitivity.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

namespace {

bool IsAssertionStatement(const Stmt* s) {
  return s->kind == StmtKind::kAssertImmediate ||
         s->kind == StmtKind::kAssumeImmediate ||
         s->kind == StmtKind::kCoverImmediate || s->kind == StmtKind::kExpect;
}

bool IsProceduralConcurrent(const Stmt* s) {
  return s != nullptr && s->is_procedural_concurrent && IsAssertionStatement(s);
}

void CollectProceduralAssertions(Stmt* s, std::vector<Stmt*>& out) {
  if (s == nullptr) return;
  if (IsProceduralConcurrent(s)) out.push_back(s);
  ForEachChildStmt(
      s, [&out](Stmt* const& sub) { CollectProceduralAssertions(sub, out); });
}

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

std::vector<EventExpr> InferredClockOf(
    const Stmt* body, const std::vector<EventExpr>& sensitivity, bool is_star,
    const RtlirModule* mod) {
  ProcedureTiming timing;
  ScanTiming(body, timing);
  if (timing.blocking) return {};
  const std::vector<EventExpr>* events = nullptr;
  if (!sensitivity.empty() && !is_star) {
    if (!timing.event_controls.empty()) return {};
    events = &sensitivity;
  } else if (timing.event_controls.size() == 1 &&
             !timing.event_controls[0]->is_star_event) {
    events = &timing.event_controls[0]->events;
  } else {
    return {};
  }
  std::unordered_set<std::string> references;
  CollectReferences(body, references);
  std::vector<EventExpr> clock;
  for (const EventExpr& ev : *events) {
    if (QualifiesAsClock(ev, mod, references)) clock.push_back(ev);
  }
  if (clock.size() != 1) return {};
  return clock;
}

std::vector<EventExpr> InferredProcedureClock(const ModuleItem* procedure,
                                              const RtlirModule* mod) {
  return InferredClockOf(procedure->body, procedure->sensitivity,
                         procedure->is_star_sensitivity, mod);
}

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

bool TakesInferredClock(Stmt* stmt, const std::vector<EventExpr>& inferred,
                        const PropertyRegistry& registry, DiagEngine& diag) {
  if (!stmt->assert_clock.empty() || inferred.empty() ||
      TreeNamesOnlyClock(stmt->assert_property, inferred, registry)) {
    return true;
  }
  diag.Error(stmt->range.start,
             "a multiclocked property may not take a contextually inferred "
             "leading clocking event",
             Subclause("16.16"));
  stmt->is_concurrent_clocked = false;
  return false;
}

void ResolveProceduralClock(Stmt* stmt, const std::vector<EventExpr>& context,
                            const PropertyRegistry& registry,
                            DiagEngine& diag) {
  if (stmt->assert_clock.empty()) {
    stmt->assert_clock = context;
    stmt->assert_clock_inferred = !context.empty();
  }
  if (!stmt->assert_clock.empty()) {
    if (!HasUniqueSemanticLeadingClock(stmt->assert_property,
                                       stmt->assert_clock, registry)) {
      diag.Error(stmt->range.start,
                 "the property has no unique semantic leading clock",
                 Subclause("16.16.1"));
      stmt->is_concurrent_clocked = false;
    }
    return;
  }
  diag.Error(stmt->range.start,
             "no clock is inferred for the procedural concurrent assertion: "
             "its property_spec opens with no clocking event, the procedure "
             "gives it none, holding a blocking timing control, more or fewer "
             "event controls than one or no unique event expression of the "
             "form the clause names, and the scope has no default clocking",
             Subclause("16.14.6"));
}

void SubstitutePropertyBody(Stmt* stmt, const ModuleItem* decl,
                            const PropertyRegistry& registry, Arena& arena) {
  Expr* instance = stmt->assert_expr;
  ActualsByFormal actuals = BindActualsWithDefaults(
      decl->prop_formals, decl->prop_formal_defaults, instance);
  if (TakesBooleanSubstitution(instance, decl)) {
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
  stmt->assert_clock = PropertyInstanceClock(decl, actuals, registry, arena);
}

void SubstituteInstance(Stmt* stmt, const PropertyRegistry& registry,
                        const InferredAtInstance& inferred, Arena& arena,
                        DiagEngine& diag) {
  if (stmt->assert_property != nullptr || stmt->assert_sequence != nullptr) {
    return;
  }
  Expr* instance = QualifiedInstance(stmt->assert_expr, registry, arena);
  const ModuleItem* seq =
      InstantiatedDecl(instance, ModuleItemKind::kSequenceDecl, registry);
  InferredAtInstance here = inferred;
  if (!stmt->assert_clock.empty()) here.clock = stmt->assert_clock;
  FillInferredDefaults(
      instance,
      seq != nullptr
          ? seq
          : InstantiatedDecl(instance, ModuleItemKind::kPropertyDecl, registry),
      here, arena, &diag);
  if (seq != nullptr) {
    stmt->assert_property = arena.Create<PropertyExprNode>();
    stmt->assert_property->kind = PropertyExprNode::Kind::kSequence;
    stmt->assert_property->sequence = SequenceInstanceBody(instance, arena);
    if (stmt->assert_clock.empty()) {
      stmt->assert_clock =
          SequenceInstanceClock(seq, instance, registry, arena);
    }
    return;
  }
  const ModuleItem* decl =
      InstantiatedDecl(instance, ModuleItemKind::kPropertyDecl, registry);
  if (decl == nullptr) return;
  stmt->assert_instance = instance;
  if (!BodyIsRead(stmt, decl, diag)) return;
  SubstitutePropertyBody(stmt, decl, registry, arena);
}

struct ProcedureContext {
  std::vector<EventExpr> inferred;
  InferredAtInstance at_instance;
};

ProcedureContext ContextOf(std::vector<EventExpr> inferred,
                           const RtlirModule* mod) {
  ProcedureContext context;
  context.at_instance.clock =
      inferred.empty() ? DefaultClockingEvent(mod) : inferred;
  context.at_instance.disable =
      mod != nullptr ? mod->default_disable_iff : nullptr;
  context.inferred = std::move(inferred);
  return context;
}

void ResolveProceduralAssertions(const std::vector<Stmt*>& assertions,
                                 const ProcedureContext& context,
                                 const PropertyRegistry& registry, Arena& arena,
                                 DiagEngine& diag) {
  const std::vector<EventExpr>& inferred = context.inferred;
  const InferredAtInstance& at_instance = context.at_instance;
  for (Stmt* stmt : assertions) {
    if (!stmt->is_concurrent_clocked) continue;
    SubstituteInstance(stmt, registry, at_instance, arena, diag);
    if (!stmt->is_concurrent_clocked) continue;
    if (stmt->assert_disable_iff == nullptr) {
      stmt->assert_disable_iff = at_instance.disable;
    }
    PromoteSequenceInstances(stmt->assert_property, registry, arena);
    if (!TakesInferredClock(stmt, inferred, registry, diag)) continue;
    ResolveProceduralClock(stmt, at_instance.clock, registry, diag);
    stmt->assert_clock_from_default_clocking =
        stmt->assert_clock_inferred && inferred.empty();
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
  ResolveProceduralAssertions(
      assertions, ContextOf(InferredProcedureClock(procedure, mod), mod),
      registry, arena, diag);
}

std::vector<EventExpr> ProcessInferredClock(const RtlirProcess& proc,
                                            const RtlirModule* mod) {
  return InferredClockOf(proc.body, proc.sensitivity, proc.is_star_sensitivity,
                         mod);
}

InferredAtInstance InferredInProcedure(const ModuleItem* procedure,
                                       const RtlirModule* mod) {
  return ContextOf(InferredProcedureClock(procedure, mod), mod).at_instance;
}

namespace {

bool IsUnclockedSampledValueCall(const Expr* e) {
  static constexpr std::array<std::string_view, 5> kNames{
      "$past", "$rose", "$fell", "$stable", "$changed"};
  return e->kind == ExprKind::kSystemCall && e->sampled_clock == nullptr &&
         std::ranges::find(kNames, e->callee) != kNames.end();
}

bool HoldsUnclockedSampledValueCall(const Expr* e) {
  if (e == nullptr) return false;
  return IsUnclockedSampledValueCall(e) ||
         AnyExprChild(e, [](const Expr* child) {
           return HoldsUnclockedSampledValueCall(child);
         });
}

void ReportUnclockedLetNames(const Expr* e,
                             const std::unordered_set<std::string_view>& lets,
                             DiagEngine& diag) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kIdentifier && lets.contains(e->text)) {
    diag.Error(e->range.start,
               std::format("no clock is inferred where let '{}' is "
                           "instantiated for the sampled value call its body "
                           "holds",
                           e->text),
               Subclause("11.12"));
  }
  ForEachExprChild(e, [&lets, &diag](const Expr* child) {
    ReportUnclockedLetNames(child, lets, diag);
  });
}

void ReportUnclockedLetInstances(
    const Stmt* s, const std::unordered_set<std::string_view>& lets,
    DiagEngine& diag) {
  if (s == nullptr || IsProceduralConcurrent(s)) return;
  ForEachChildExpr(s, [&lets, &diag](Expr* const& e) {
    ReportUnclockedLetNames(e, lets, diag);
  });
  ForEachChildStmt(s, [&lets, &diag](Stmt* const& sub) {
    ReportUnclockedLetInstances(sub, lets, diag);
  });
}

}  // namespace

void ReportUnclockedLetSampledValues(const ModuleItem* procedure,
                                     const RtlirModule* mod, DiagEngine& diag) {
  std::unordered_set<std::string_view> lets;
  for (const ModuleItem* let : mod->let_decls) {
    if (HoldsUnclockedSampledValueCall(let->init_expr)) lets.insert(let->name);
  }
  if (lets.empty() || !InferredInProcedure(procedure, mod).clock.empty())
    return;
  ReportUnclockedLetInstances(procedure->body, lets, diag);
}

void ElaborateSubroutineConcurrentAssertions(ModuleItem* subroutine,
                                             const RtlirModule* mod,
                                             const PropertyRegistry& registry,
                                             Arena& arena, DiagEngine& diag) {
  std::vector<Stmt*> assertions;
  for (Stmt* s : subroutine->func_body_stmts) {
    CollectProceduralAssertions(s, assertions);
  }
  if (assertions.empty()) return;
  ResolveProceduralAssertions(assertions, ContextOf({}, mod), registry, arena,
                              diag);
}

}  // namespace delta
