#include <initializer_list>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/concurrent_assertion_expr.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/global_clock_assertion_event.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

namespace {

// §16.14.3: the optional pass statement (statement_or_null) of a cover
// statement shall not include any concurrent assert, assume, or cover
// statement. A procedural concurrent assertion is parsed as an
// assert/assume/cover-immediate Stmt that carries is_procedural_concurrent;
// ordinary immediate assertions leave that flag clear and remain permitted.
// Walk the pass-statement subtree — including the statements a block, fork,
// conditional, loop, or case nests — and return the first offending statement,
// or nullptr when the pass statement contains none.
const Stmt* FindConcurrentAssertionInPassStmt(const Stmt* s);

// The first procedural concurrent assertion reachable from any statement in
// `children`, or null when none of them contains one.
template <typename Stmts>
const Stmt* FindConcurrentAssertionInStmtList(const Stmts& children) {
  for (const Stmt* child : children) {
    if (const Stmt* hit = FindConcurrentAssertionInPassStmt(child)) return hit;
  }
  return nullptr;
}

const Stmt* FindConcurrentAssertionInPassStmt(const Stmt* s) {
  if (s == nullptr) return nullptr;
  if (s->is_procedural_concurrent && (s->kind == StmtKind::kAssertImmediate ||
                                      s->kind == StmtKind::kAssumeImmediate ||
                                      s->kind == StmtKind::kCoverImmediate)) {
    return s;
  }
  if (const Stmt* hit = FindConcurrentAssertionInStmtList(s->stmts)) return hit;
  if (const Stmt* hit = FindConcurrentAssertionInStmtList(s->fork_stmts))
    return hit;
  const std::initializer_list<const Stmt*> kBranches = {
      s->then_branch, s->else_branch,      s->body,
      s->for_body,    s->assert_pass_stmt, s->assert_fail_stmt};
  if (const Stmt* hit = FindConcurrentAssertionInStmtList(kBranches))
    return hit;
  for (const CaseItem& ci : s->case_items) {
    if (const Stmt* hit = FindConcurrentAssertionInPassStmt(ci.body))
      return hit;
  }
  return nullptr;
}

// §16.6: an expression appearing in a concurrent assertion shall not reference
// a variable of chandle type. A concurrent assertion statement
// (assert/assume/cover/restrict property) keeps its property_spec expression in
// assert_expr, or, for the simple clocked boolean form, in the immediate body
// statement's assert_expr. Reports the first chandle reference once.
void CheckConcurrentAssertionNoChandle(const ModuleItem* item,
                                       const RtlirModule* mod,
                                       DiagEngine& diag) {
  const Expr* bodies[] = {item->assert_expr, item->body != nullptr
                                                 ? item->body->assert_expr
                                                 : nullptr};
  for (const Expr* b : bodies) {
    std::string_view ch = ConcurrentAssertionExprReferencedChandle(b, mod);
    if (!ch.empty()) {
      diag.Error(item->loc,
                 "concurrent assertion expression references chandle "
                 "variable \"" +
                     std::string(ch) + "\"",
                 Subclause("16.6"));
      return;
    }
  }
}

bool IsStaticDeferredAssertion(const ModuleItem* item) {  // §16.4.3
  return item->body != nullptr && item->body->is_deferred;
}

}  // namespace

void Elaborator::ElaborateSequenceDeclItem(ModuleItem* item, RtlirModule* mod) {
  sequence_names_.insert(item->name);
  mod->sequence_decls.push_back(item);
  // §16.8: a cyclic dependency among named sequences is an error. All sequence
  // decls are registered before elaboration (see ElaborateModule), so this DFS
  // sees the full graph regardless of declaration order.
  if (property_registry_.HasCyclicSequenceDependency(item)) {
    diag_.Error(item->loc,
                "cyclic dependency among named sequences involving \"" +
                    std::string(item->name) + "\"",
                Subclause("16.8"));
  }
  // §16.10: a formal-argument name may not be redeclared as a body local.
  ValidateNoFormalShadowedByBodyLocal(item);
  ValidateClockingBlock(item, mod);
}

// §16.12.1: an instance of a named property used as a property_expr operand of
// any property-building operator must, once substituted, yield a legal
// property_expr. A disable iff clause makes the flattened body a property_spec,
// which is not a legal operand -- so such a property may not carry a disable
// iff clause when it appears as an operand. The parser records the instances
// that stand as the operand of a prefix or infix property operator (not,
// s_nexttime, s_eventually, s_always, and the right operand of
// s_until/s_until_with) in prop_negated_instance_refs.
void Elaborator::CheckPropertyOperandInstances(const ModuleItem* item) {
  for (auto operand_ref : item->prop_negated_instance_refs) {
    const ModuleItem* callee = property_registry_.Find(operand_ref);
    if (callee == nullptr || callee->kind != ModuleItemKind::kPropertyDecl) {
      continue;
    }
    if (property_registry_.FlattenedDisableIffCount(callee) > 0) {
      diag_.Error(item->loc,
                  "property \"" + std::string(operand_ref) +
                      "\" has a disable iff clause and cannot be used as an "
                      "operand of a property operator in \"" +
                      std::string(item->name) + "\"",
                  Subclause("16.12.1"));
    }
  }
}

void Elaborator::ElaboratePropertyDeclItem(ModuleItem* item, RtlirModule* mod) {
  // §16.12: nesting of disable iff (explicitly or via property instantiation)
  // is forbidden; the §F.4.1 flattened count catches both.
  if (property_registry_.FlattenedDisableIffCount(item) > 1) {
    diag_.Error(item->loc,
                "property \"" + std::string(item->name) +
                    "\" nests disable iff clauses",
                Subclause("16.12"));
  }
  CheckPropertyOperandInstances(item);
  // §16.10: a formal-argument name may not be redeclared as a body local.
  ValidateNoFormalShadowedByBodyLocal(item);
  // §16.12.17 / §F.7: enforce the restrictions on recursive properties.
  ValidateRecursiveProperty(item);
  ValidateClockingBlock(item, mod);
}

void Elaborator::ElaborateAssertPropertyItem(ModuleItem* item,
                                             RtlirModule* mod) {
  CheckConcurrentAssertionNoChandle(item, mod, diag_);
  const ProcessBuildEnv kEnv{arena_, diag_, &func_decls_, &const_names_};
  // §16.4.3: a module-item deferred immediate assertion is a static deferred
  // assertion, modeled as an implicit always_comb procedure.
  if (IsStaticDeferredAssertion(item)) {
    AddProcess(RtlirProcessKind::kAlwaysComb, item, mod, kEnv);
    return;
  }
  // §16.5.2: `assert property(@$global_clock a);` under a
  // `global clocking @clk; endclocking` declaration is logically equivalent to
  // `assert property(@clk a);`, so the assertion's leading clocking event is
  // the event that declaration names. The rewrite runs before the process is
  // built so the clock the process waits on, and the §9.2.2.4 checks the
  // process is held to, both see the event that was substituted in.
  if (module_global_clocking_event_ != nullptr) {
    SubstituteGlobalClockLeadingEvent(item->sensitivity,
                                      *module_global_clocking_event_);
  }
  // §16.14.5: a static concurrent assertion outside procedural code uses
  // `always` semantics. The parser captures the simple clocked boolean form as
  // a leading clock in item->sensitivity plus an immediate-assert body in
  // item->body; model it as a clocked process so the property is checked at
  // each leading clock edge.
  if (item->body != nullptr && !item->sensitivity.empty()) {
    AddProcess(RtlirProcessKind::kAlwaysFF, item, mod, kEnv);
    return;
  }
  ValidateClockingBlock(item, mod);
}

bool Elaborator::ElaborateAssertionItem(ModuleItem* item, RtlirModule* mod) {
  switch (item->kind) {
    case ModuleItemKind::kSequenceDecl:
      ElaborateSequenceDeclItem(item, mod);
      return true;
    case ModuleItemKind::kPropertyDecl:
      ElaboratePropertyDeclItem(item, mod);
      return true;
    case ModuleItemKind::kAssertProperty:
      ElaborateAssertPropertyItem(item, mod);
      return true;
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kCoverSequence:
      // §16.14.3: a cover statement's optional pass statement shall not include
      // any concurrent assert, assume, or cover statement.
      if (FindConcurrentAssertionInPassStmt(item->assert_pass_stmt) !=
          nullptr) {
        diag_.Error(item->loc,
                    "the pass statement of a cover statement may not include a "
                    "concurrent assert, assume, or cover statement",
                    Subclause("16.14.3"));
      }
      ValidateClockingBlock(item, mod);
      return true;
    case ModuleItemKind::kAssumeProperty:
    case ModuleItemKind::kRestrictProperty:
    case ModuleItemKind::kClockingBlock:
      ValidateClockingBlock(item, mod);
      return true;
    default:
      // §23.10.4 kDefparam, kExportDecl, kDefaultDisableIff, kNestedModuleDecl,
      // and any remaining kind are no-ops at behavioral elaboration.
      return true;
  }
}

}  // namespace delta
