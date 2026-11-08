#include <algorithm>
#include <array>
#include <format>
#include <span>
#include <string_view>

#include "common/diagnostic.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

bool IsForHeaderStmt(const Stmt* s, const Stmt* sub) {
  for (const auto* init : s->for_inits)
    if (init == sub) return true;
  for (const auto* step : s->for_steps)
    if (step == sub) return true;
  return false;
}

bool StmtContainsBlockingAssignment(const Stmt* stmt) {
  if (stmt == nullptr) return false;
  if (stmt->kind == StmtKind::kBlockingAssign) return true;
  bool found = false;
  ForEachChildStmt(stmt, [&](Stmt* const& sub) {
    if (found || IsForHeaderStmt(stmt, sub)) return;
    found = StmtContainsBlockingAssignment(sub);
  });
  return found;
}

bool StmtContainsNonEventTimingControl(const Stmt* stmt) {
  if (stmt == nullptr) return false;
  switch (stmt->kind) {
    case StmtKind::kDelay:
    case StmtKind::kCycleDelay:
    case StmtKind::kWait:
    case StmtKind::kWaitFork:
      return true;
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
      if (stmt->delay != nullptr || stmt->cycle_delay != nullptr) return true;
      break;
    default:
      break;
  }
  bool found = false;
  ForEachChildStmt(stmt, [&](Stmt* const& sub) {
    if (found) return;
    found = StmtContainsNonEventTimingControl(sub);
  });
  return found;
}

constexpr std::array kInitialForbidden{StmtKind::kIf,
                                       StmtKind::kCase,
                                       StmtKind::kFor,
                                       StmtKind::kForeach,
                                       StmtKind::kWhile,
                                       StmtKind::kForever,
                                       StmtKind::kRepeat,
                                       StmtKind::kDoWhile,
                                       StmtKind::kBreak,
                                       StmtKind::kContinue,
                                       StmtKind::kReturn,
                                       StmtKind::kBlockingAssign,
                                       StmtKind::kNonblockingAssign,
                                       StmtKind::kExprStmt,
                                       StmtKind::kFork,
                                       StmtKind::kDisable,
                                       StmtKind::kDisableFork,
                                       StmtKind::kEventTrigger,
                                       StmtKind::kNbEventTrigger,
                                       StmtKind::kAssign,
                                       StmtKind::kDeassign,
                                       StmtKind::kForce,
                                       StmtKind::kRelease,
                                       StmtKind::kRandcase,
                                       StmtKind::kRandsequence,
                                       StmtKind::kExpect};

constexpr std::array kAlwaysForbidden{
    StmtKind::kReturn,      StmtKind::kFork,         StmtKind::kDisable,
    StmtKind::kDisableFork, StmtKind::kEventTrigger, StmtKind::kNbEventTrigger,
    StmtKind::kAssign,      StmtKind::kDeassign,     StmtKind::kForce,
    StmtKind::kRelease,     StmtKind::kRandcase,     StmtKind::kRandsequence,
    StmtKind::kExpect};

void ReportForbiddenStatements(const Stmt* s,
                               std::span<const StmtKind> forbidden,
                               std::string_view form, const ModuleDecl* decl,
                               DiagEngine& diag) {
  if (s == nullptr) return;
  if (std::ranges::find(forbidden, s->kind) != forbidden.end()) {
    diag.Error(s->range.start,
               std::format("this statement is none of those an {} procedure "
                           "of checker '{}' may hold",
                           form, decl->name),
               Subclause("17.5"));
  }
  if (s->kind == StmtKind::kAssertImmediate ||
      s->kind == StmtKind::kAssumeImmediate ||
      s->kind == StmtKind::kCoverImmediate) {
    return;
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    ReportForbiddenStatements(sub, forbidden, form, decl, diag);
  });
}

void CheckProcedureStatements(const ModuleItem* item, const ModuleDecl* decl,
                              DiagEngine& diag) {
  if (item->kind == ModuleItemKind::kInitialBlock) {
    ReportForbiddenStatements(item->body, kInitialForbidden, "initial", decl,
                              diag);
  }
  if (item->kind == ModuleItemKind::kAlwaysCombBlock ||
      item->kind == ModuleItemKind::kAlwaysLatchBlock ||
      item->kind == ModuleItemKind::kAlwaysFFBlock) {
    ReportForbiddenStatements(item->body, kAlwaysForbidden, "always", decl,
                              diag);
  }
}

}  // namespace

void CheckCheckerBodyItemRules(const ModuleItem* item, const ModuleDecl* decl,
                               bool parent_is_checker, DiagEngine& diag) {
  if (!parent_is_checker) return;
  for (const auto* sub : item->gen_body) {
    CheckCheckerBodyItemRules(sub, decl, parent_is_checker, diag);
  }
  if (item->gen_else != nullptr) {
    CheckCheckerBodyItemRules(item->gen_else, decl, parent_is_checker, diag);
  }
  for (const auto& arm : item->gen_case_items) {
    for (const auto* sub : arm.body) {
      CheckCheckerBodyItemRules(sub, decl, parent_is_checker, diag);
    }
  }
  if (item->kind == ModuleItemKind::kNetDecl) {
    diag.Error(item->loc,
               std::format("a net cannot be declared inside checker '{}'; "
                           "only variables may be defined in a checker body",
                           decl->name),
               Subclause("17.7"));
  }
  if (item->kind == ModuleItemKind::kAlwaysBlock) {
    diag.Error(item->loc,
               std::format("a general 'always' procedure cannot be used "
                           "inside checker '{}'; use always_comb, "
                           "always_latch, or always_ff instead",
                           decl->name),
               Subclause("17.5"));
  }
  if (item->kind == ModuleItemKind::kAlwaysFFBlock &&
      StmtContainsBlockingAssignment(item->body)) {
    diag.Error(item->loc,
               std::format("a blocking assignment cannot appear in an "
                           "always_ff procedure of checker '{}'; use a "
                           "nonblocking assignment, or move it to an "
                           "always_comb or always_latch procedure",
                           decl->name),
               Subclause("17.7.1"));
  }
  if (item->kind == ModuleItemKind::kInitialBlock &&
      StmtContainsNonEventTimingControl(item->body)) {
    diag.Error(item->loc,
               std::format("an initial procedure in checker '{}' may use only "
                           "an event control for timing; a delay, a cycle "
                           "delay and a wait are not allowed",
                           decl->name),
               Subclause("17.5"));
  }
  CheckProcedureStatements(item, decl, diag);
  if (item->kind == ModuleItemKind::kNestedModuleDecl &&
      item->nested_module_decl &&
      item->nested_module_decl->decl_kind != ModuleDeclKind::kChecker) {
    diag.Error(item->loc,
               std::format("a module, interface, or program cannot be "
                           "declared inside checker '{}'",
                           decl->name),
               Subclause("17.2"));
  }
}

}  // namespace delta
