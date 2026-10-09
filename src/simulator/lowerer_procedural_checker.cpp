#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_checker_site.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"
#include "simulator/assertion_read_names.h"
#include "simulator/checker_actuals.h"
#include "simulator/lowerer.h"
#include "simulator/procedural_assertion.h"
#include "simulator/process.h"
#include "simulator/sequence_flatten.h"

namespace delta {

// §17.3: a static assertion of a procedural checker is treated as if it
// stood at the instantiation, a concurrent one as a procedural concurrent
// assertion on the clock it names, with the checker's formals substituted
// for an event actual as a static checker's process has them. The statement
// is copied for the instance, so that two instances of one checker reached
// by one procedure keep a queue each.
bool Lowerer::KeepProceduralCheckerAssertion(const RtlirProcess& proc) {
  if (procedural_checker_root_.empty() || !proc.is_static_assertion) {
    return false;
  }
  RecordAssertionSampleScope(proc);
  auto* stmt = arena_.Create<Stmt>(*proc.body);
  if (stmt->is_concurrent_clocked) {
    stmt->is_procedural_concurrent = true;
    stmt->assert_clock = SubstituteClock(
        stmt->assert_clock, CheckerTreeActuals(inst_prefix_, ctx_), arena_);
  }
  // §17.3 with §16.14.6.1: the instance's own assertions read in a formal's
  // place the actual whose locals and const casts are saved as it is queued.
  std::vector<const Expr*> saved_actuals;
  auto it = procedural_checker_actuals_.find(inst_prefix_);
  if (it != procedural_checker_actuals_.end()) {
    SubstituteActualsInAssertion(*stmt, it->second, arena_);
    for (const auto& entry : it->second) saved_actuals.push_back(entry.second);
  }
  procedural_checker_assertions_[procedural_checker_root_].push_back(
      StartProceduralCheckerAssertion(stmt, inst_prefix_,
                                      std::move(saved_actuals), ctx_, arena_));
  return true;
}

void Lowerer::RecordProceduralCheckerActuals(const RtlirModuleInst& inst,
                                             const std::string& child_prefix) {
  if (!inst.is_procedural || !inst.resolved->is_checker) return;
  ActualsByFormal actuals;
  std::unordered_set<std::string> names;
  for (const RtlirPortBinding& binding : inst.port_bindings) {
    Expr* actual = ProceduralActualInInstantiatingScope(
        binding.connection, inst_prefix_, inst.procedure_locals, arena_);
    if (actual == nullptr) continue;
    actuals[binding.port_name] = actual;
    CollectSampledOperandNames(actual, names);
  }
  if (actuals.empty()) return;
  procedural_checker_actuals_[child_prefix] = std::move(actuals);
  AssertionSampleScope scope;
  scope.inst_prefix = inst_prefix_;
  scope.names.assign(names.begin(), names.end());
  assertion_sample_scopes_.push_back(std::move(scope));
}

// §17.3: a procedural checker instance's static assertions, and those of
// the checkers nested in it, are kept for the procedure to queue.
void Lowerer::LowerChildBodyUnderCheckerRoot(const RtlirModuleInst& child) {
  std::string saved_root = procedural_checker_root_;
  if (child.is_procedural && saved_root.empty()) {
    procedural_checker_root_ = inst_prefix_;
  }
  LowerChildBody(child.resolved);
  procedural_checker_root_ = std::move(saved_root);
}

void Lowerer::RecordCheckerInstantiations(const RtlirProcess& proc,
                                          Process* p) {
  for (const ProceduralCheckerSite& site : proc.checker_instances) {
    checker_instantiation_links_.push_back(
        {p, site.stmt, inst_prefix_ + std::string(site.inst_name) + "."});
  }
}

void Lowerer::LinkCheckerInstantiations() {
  for (const CheckerInstantiationLink& link : checker_instantiation_links_) {
    link.process->checker_instance_assertions[link.stmt] =
        procedural_checker_assertions_[link.inst_prefix];
  }
}

}  // namespace delta
