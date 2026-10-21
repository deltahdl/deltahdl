#include "simulator/assertion_coverage.h"

#include <cstdint>
#include <functional>
#include <string>
#include <unordered_set>
#include <vector>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/code_coverage.h"
#include "simulator/code_coverage_items.h"
#include "simulator/coverage_control.h"
#include "simulator/lowerer_child.h"
#include "simulator/sim_context.h"
#include "simulator/statement_coverage.h"
#include "simulator/vpi_design_walk.h"

namespace delta {

namespace {

// §40.3.2.1 `SV_COV_RESET: an assertion reset has no outcome tallied.
void ClearTallies(AssertionTally& tally) {
  const bool kCoverSequence = tally.counts.is_cover_sequence;
  tally.counts = {};
  tally.counts.is_cover_sequence = kCoverSequence;
}

// §40.2.2: an assertion is covered once it has had at least one success - a
// nonvacuous one, or a match of a cover sequence, as vpiCovered reads it.
bool Covers(const AssertionCoverageCounters& counts) {
  return counts.successes > 0;
}

bool IsAssertion(const Stmt* stmt) {
  return stmt->kind == StmtKind::kAssertImmediate ||
         stmt->kind == StmtKind::kAssumeImmediate ||
         stmt->kind == StmtKind::kCoverImmediate;
}

// The number of starts and stops of `scope`'s assertion coverage, which
// changes whenever its collection does.
std::uint64_t CollectionEpoch(const std::string& scope,
                              const CoverageControlState& cov) {
  return cov.StartCount(scope, kCoverageTypeAssertion) +
         cov.StopCount(scope, kCoverageTypeAssertion);
}

// §40.5.3 with §40.3.2.1: whether `tally` is collected - as a start or a stop
// through its handle left it, where its instance's collection has not changed
// since, and otherwise as its instance's is.
bool IsCollected(const AssertionTally& tally, CoverageControlState& cov) {
  const std::string& scope = tally.instance->scope;
  const auto& overrides = cov.Code().assertion_overrides;
  auto found = overrides.find(tally.key);
  if (!tally.key.empty() && found != overrides.end() &&
      found->second.epoch == CollectionEpoch(scope, cov)) {
    return found->second.collecting;
  }
  return cov.IsCollecting(scope, kCoverageTypeAssertion);
}

// The tally `outcome` adds to.
std::uint64_t& TallyFor(AssertionCoverageCounters& counts,
                        AssertionOutcome outcome) {
  switch (outcome) {
    case AssertionOutcome::kSuccess:
      return counts.successes;
    case AssertionOutcome::kVacuousSuccess:
      return counts.vacuous_successes;
    case AssertionOutcome::kFailure:
      return counts.failures;
    case AssertionOutcome::kDisabled:
      return counts.disabled;
    case AssertionOutcome::kKilled:
      return counts.killed;
    default:
      return counts.attempts;
  }
}

// The assertions of the instance of `mod`, each once.
std::vector<const Stmt*> InstanceAssertions(const RtlirModule& mod) {
  std::vector<const Stmt*> found;
  std::unordered_set<const Stmt*> seen;
  const std::function<void(const Stmt*)> kAdd = [&](const Stmt* stmt) {
    if (IsAssertion(stmt) && seen.insert(stmt).second) found.push_back(stmt);
  };
  for (const RtlirProcess& proc : mod.processes) {
    ForEachCoverableStmt(proc.body, kAdd);
  }
  auto subroutine = [&](const ModuleItem* item) {
    if (item == nullptr) return;
    for (const Stmt* stmt : item->func_body_stmts) {
      ForEachCoverableStmt(stmt, kAdd);
    }
  };
  for (const ModuleItem* item : mod.function_decls) subroutine(item);
  for (const RtlirGenBlockSubroutine& sub : mod.gen_block_subroutines) {
    subroutine(sub.decl);
  }
  return found;
}

}  // namespace

void AttachAssertionCoverage(const RtlirDesign* design, SimContext& ctx) {
  CoverageControlState& cov = ctx.GetCoverageControlState();
  CodeCoverage& code = cov.Code();
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        const std::vector<const Stmt*> kAssertions = InstanceAssertions(*mod);
        if (kAssertions.empty()) return;
        auto& inst = code.assertion_instances.emplace_back();
        inst.scope = CoverageScopeOfInstanceKey(prefix, ctx);
        for (const Stmt* stmt : kAssertions) {
          AssertionTally& tally = code.assertion_tallies.emplace_back();
          tally.stmt = stmt;
          tally.prefix = prefix;
          tally.instance = &inst;
          tally.counts.is_cover_sequence = stmt->cover_sequence;
          inst.items.push_back(&tally);
          code.assertions[stmt].push_back(&tally);
        }
        ArmCoverageInstance(inst, kCoverageTypeAssertion,
                            static_cast<std::int64_t>(kAssertions.size()), cov);
      });
}

void NoteAssertionOutcome(const Stmt* stmt, const std::string& prefix,
                          AssertionOutcomes outcomes,
                          const std::function<std::string()>& key,
                          CoverageControlState& cov) {
  AssertionTally* tally = TallyIn(cov.Code().assertions, stmt, prefix);
  if (tally == nullptr || outcomes.count == 0) return;
  if (tally->key.empty()) tally->key = key();
  CoverageInstanceItems<AssertionTally>& inst = *tally->instance;
  ApplyCoverageResets(inst, kCoverageTypeAssertion, cov, ClearTallies);
  if (!IsCollected(*tally, cov)) return;
  const bool kWasCovered = Covers(tally->counts);
  TallyFor(tally->counts, outcomes.outcome) += outcomes.count;
  if (!kWasCovered && Covers(tally->counts)) {
    CountCoveredItem(inst, kCoverageTypeAssertion, cov);
  }
}

AssertionCoverageCounters AssertionTallies(const std::string& key,
                                           CoverageControlState& cov) {
  for (AssertionTally& tally : cov.Code().assertion_tallies) {
    if (tally.key != key) continue;
    ApplyCoverageResets(*tally.instance, kCoverageTypeAssertion, cov,
                        ClearTallies);
    return tally.counts;
  }
  return {};
}

CoverageStatus ControlAssertionCoverage(CoverageControl control,
                                        const std::string& key,
                                        const std::string& scope,
                                        CoverageControlState& cov) {
  const CoverageStatus kOffered =
      cov.Control(CoverageControl::kCheck, kCoverageTypeAssertion, scope,
                  /*include_below=*/false);
  if (kOffered != CoverageStatus::kOk && kOffered != CoverageStatus::kPartial) {
    return kOffered;
  }
  CodeCoverage& code = cov.Code();
  if (control == CoverageControl::kStart || control == CoverageControl::kStop) {
    code.assertion_overrides[key] = {control == CoverageControl::kStart,
                                     CollectionEpoch(scope, cov)};
    return CoverageStatus::kOk;
  }
  if (control != CoverageControl::kReset) return kOffered;
  for (AssertionTally& tally : code.assertion_tallies) {
    if (tally.key != key) continue;
    CoverageInstanceItems<AssertionTally>& inst = *tally.instance;
    ApplyCoverageResets(inst, kCoverageTypeAssertion, cov, ClearTallies);
    if (Covers(tally.counts)) {
      --inst.covered;
      cov.SetCoveredItems(inst.scope, kCoverageTypeAssertion, inst.covered);
    }
    ClearTallies(tally);
  }
  return CoverageStatus::kOk;
}

}  // namespace delta
