#include "simulator/statement_coverage.h"

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
#include "simulator/vpi_design_walk.h"

namespace delta {

namespace {

// §40.3.2.1 `SV_COV_RESET: a statement reset has executed no times.
void ClearExecutions(StatementTally& tally) { tally.executions = 0; }

// A.6.12: the statements a randsequence's code blocks hold, in a production
// and after a rule's weight.
void ForEachRandsequenceCode(const Stmt* stmt,
                             const std::function<void(const Stmt*)>& visit) {
  for (const auto& production : stmt->rs_productions) {
    for (const auto& rule : production.rules) {
      for (const Stmt* sub : rule.weight_code) visit(sub);
      for (const auto& prod : rule.prods) {
        for (const Stmt* sub : prod.code_stmts) visit(sub);
      }
    }
  }
}

// The statements of the subroutine `item`, where it is a task or a function.
void ForEachSubroutineStmt(const ModuleItem* item,
                           const std::function<void(const Stmt*)>& fn) {
  if (item == nullptr || (item->kind != ModuleItemKind::kFunctionDecl &&
                          item->kind != ModuleItemKind::kTaskDecl)) {
    return;
  }
  for (const Stmt* stmt : item->func_body_stmts) ForEachCoverableStmt(stmt, fn);
}

// The statements of the instance of `mod`, each once: those of its
// procedures, but not of the processes that carry an assertion written as a
// module item, which is no statement, and those of its tasks and functions,
// its generate blocks' among them.
std::vector<const Stmt*> InstanceStatements(const RtlirModule& mod) {
  std::vector<const Stmt*> stmts;
  std::unordered_set<const Stmt*> seen;
  const std::function<void(const Stmt*)> kAdd = [&](const Stmt* stmt) {
    if (seen.insert(stmt).second) stmts.push_back(stmt);
  };
  for (const RtlirProcess& proc : mod.processes) {
    if (!proc.is_static_assertion) ForEachCoverableStmt(proc.body, kAdd);
  }
  for (const ModuleItem* item : mod.function_decls) {
    ForEachSubroutineStmt(item, kAdd);
  }
  for (const RtlirGenBlockSubroutine& sub : mod.gen_block_subroutines) {
    ForEachSubroutineStmt(sub.decl, kAdd);
  }
  return stmts;
}

}  // namespace

void ForEachCoverableStmt(const Stmt* stmt,
                          const std::function<void(const Stmt*)>& fn) {
  if (stmt == nullptr) return;
  if (stmt->kind != StmtKind::kVarDecl &&
      stmt->kind != StmtKind::kBlockItemDecl) {
    fn(stmt);
  }
  const std::function<void(const Stmt*)> kVisit = [&fn](const Stmt* sub) {
    ForEachCoverableStmt(sub, fn);
  };
  for (const Stmt* sub : stmt->stmts) kVisit(sub);
  for (const Stmt* sub : stmt->fork_stmts) kVisit(sub);
  kVisit(stmt->then_branch);
  kVisit(stmt->else_branch);
  kVisit(stmt->body);
  kVisit(stmt->for_body);
  kVisit(stmt->assert_pass_stmt);
  kVisit(stmt->assert_fail_stmt);
  for (const CaseItem& item : stmt->case_items) kVisit(item.body);
  for (const auto& item : stmt->randcase_items) kVisit(item.second);
  ForEachRandsequenceCode(stmt, kVisit);
}

void AttachStatementCoverage(const RtlirDesign* design, SimContext& ctx) {
  CoverageControlState& cov = ctx.GetCoverageControlState();
  CodeCoverage& code = cov.Code();
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        const std::vector<const Stmt*> kStmts = InstanceStatements(*mod);
        if (kStmts.empty()) return;
        auto& inst = code.statement_instances.emplace_back();
        inst.scope = CoverageScopeOfInstanceKey(prefix, ctx);
        for (const Stmt* stmt : kStmts) {
          StatementTally& tally = code.statement_tallies.emplace_back();
          tally.stmt = stmt;
          tally.prefix = prefix;
          tally.instance = &inst;
          inst.items.push_back(&tally);
          code.statements[stmt].push_back(&tally);
        }
        ArmCoverageInstance(inst, kCoverageTypeStatement,
                            static_cast<std::int64_t>(kStmts.size()), cov);
      });
}

void NoteStatementExecuted(const Stmt* stmt, SimContext& ctx) {
  CoverageControlState& cov = ctx.GetCoverageControlState();
  CodeCoverage& code = cov.Code();
  if (!code.statements.contains(stmt)) return;
  StatementTally* tally =
      TallyIn(code.statements, stmt,
              CoverageInstancePrefix(ctx.ActiveInstancePrefix()));
  if (tally == nullptr) return;
  CoverageInstanceItems<StatementTally>& inst = *tally->instance;
  ApplyCoverageResets(inst, kCoverageTypeStatement, cov, ClearExecutions);
  if (!cov.IsCollecting(inst.scope, kCoverageTypeStatement)) return;
  if (tally->executions++ == 0) {
    CountCoveredItem(inst, kCoverageTypeStatement, cov);
  }
}

EntityCoverage StatementHandleCoverage(const Stmt* stmt,
                                       const std::string& prefix,
                                       CoverageControlState& cov) {
  CodeCoverage& code = cov.Code();
  EntityCoverage entities;
  const std::function<void(const Stmt*)> kCount = [&](const Stmt* held) {
    StatementTally* tally = TallyIn(code.statements, held, prefix);
    if (tally == nullptr) return;
    ApplyCoverageResets(*tally->instance, kCoverageTypeStatement, cov,
                        ClearExecutions);
    ++entities.total;
    if (tally->executions > 0) ++entities.covered;
    entities.hit_count += tally->executions;
  };
  if (stmt->kind != StmtKind::kBlock && stmt->kind != StmtKind::kFork) {
    ForEachCoverableStmt(stmt, kCount);
    return entities;
  }
  for (const Stmt* held : stmt->stmts) ForEachCoverableStmt(held, kCount);
  for (const Stmt* held : stmt->fork_stmts) ForEachCoverableStmt(held, kCount);
  return entities;
}

}  // namespace delta
