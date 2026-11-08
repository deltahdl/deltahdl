#include <cstdint>
#include <format>
#include <optional>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/class_method_reads.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

static bool FindEnclosing(const ModuleDecl* scope, const ModuleDecl* decl,
                          std::vector<const ModuleDecl*>& path) {
  for (const ModuleItem* item : scope->items) {
    const ModuleDecl* nested = item->nested_module_decl;
    if (nested == nullptr) continue;
    if (nested == decl || FindEnclosing(nested, decl, path)) {
      path.push_back(scope);
      return true;
    }
  }
  return false;
}

std::vector<const ModuleDecl*> EnclosingDecls(const CompilationUnit* unit,
                                              const ModuleDecl* decl) {
  std::vector<const ModuleDecl*> path;
  if (unit == nullptr) return path;
  for (const auto* scopes :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const ModuleDecl* scope : *scopes) {
      if (FindEnclosing(scope, decl, path)) return path;
    }
  }
  return path;
}

static void ReportNegativeCycleDelays(const Stmt* s, const ScopeMap& scope,
                                      DiagEngine& diag) {
  if (s == nullptr) return;
  if (s->cycle_delay != nullptr) {
    std::optional<int64_t> count = ConstEvalInt(s->cycle_delay, scope);
    if (count.has_value() && *count < 0) {
      diag.Error(s->cycle_delay->range.start,
                 std::format("cycle delay (##) value is negative ({}); a "
                             "cycle delay counts zero or more clocking events",
                             *count),
                 Subclause("14.11"));
    }
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    ReportNegativeCycleDelays(sub, scope, diag);
  });
}

void ValidateCycleDelayCounts(const ModuleDecl* decl, const ScopeMap& scope,
                              DiagEngine& diag) {
  std::vector<ProceduralRoot> roots;
  CollectProceduralRoots(decl->items, roots);
  for (const auto& root : roots) {
    ReportNegativeCycleDelays(root.body, scope, diag);
  }
}

namespace {

void CollectClockingBlocks(const std::vector<ModuleItem*>& items,
                           std::vector<const ModuleItem*>& out) {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kClockingBlock) out.push_back(item);
    CollectClockingBlocks(item->gen_body, out);
    if (item->gen_else != nullptr) {
      CollectClockingBlocks(item->gen_else->gen_body, out);
    }
    for (const auto& ci : item->gen_case_items) {
      CollectClockingBlocks(ci.body, out);
    }
  }
}

struct ProceduralOnlyHeads {
  std::unordered_set<std::string_view> dynamic_arrays;
  const std::unordered_set<std::string_view>& class_vars;
  const std::unordered_set<std::string_view>& auto_subroutines;
};

bool IsIdentIn(const Expr* e, const std::unordered_set<std::string_view>& set) {
  return e != nullptr && e->kind == ExprKind::kIdentifier &&
         set.contains(e->text);
}

bool DesignatesProceduralOnly(const Expr* e, const ProceduralOnlyHeads& heads) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kSelect &&
      IsIdentIn(e->base, heads.dynamic_arrays)) {
    return true;
  }
  if (e->kind == ExprKind::kMemberAccess &&
      (IsIdentIn(e->lhs, heads.class_vars) ||
       IsIdentIn(e->lhs, heads.auto_subroutines))) {
    return true;
  }
  return AnyExprChild(e, [&heads](const Expr* child) {
    return DesignatesProceduralOnly(child, heads);
  });
}

ScopeNameSet ClockingSignalScope(const CompilationUnit* unit,
                                 const ModuleDecl* decl) {
  ScopeNameSet names;
  names.AddScope(decl);
  for (const ModuleDecl* outer : EnclosingDecls(unit, decl)) {
    names.AddScope(outer);
  }
  if (unit != nullptr) {
    for (const ModuleItem* item : unit->cu_items) names.AddItem(item);
    for (const PackageDecl* pkg : unit->packages) {
      for (const ModuleItem* item : pkg->items) names.AddItem(item);
    }
  }
  return names;
}

void ReportUndeclaredClockingEvent(const ModuleItem* block,
                                   const ScopeNameSet& names,
                                   DiagEngine& diag) {
  std::vector<const Expr*> refs;
  for (const EventExpr& ev : block->clocking_event) {
    CollectBareIdents(ev.signal, refs);
    CollectBareIdents(ev.iff_condition, refs);
  }
  for (const Expr* ref : refs) {
    if (names.Contains(ref->text)) continue;
    diag.Error(
        ref->range.start,
        std::format("reference to unresolved identifier '{}'", ref->text),
        Subclause("23.9"));
  }
}

}  // namespace

void Elaborator::ValidateClockingSignalTargets(const ModuleDecl* decl) {
  std::vector<const ModuleItem*> blocks;
  CollectClockingBlocks(decl->items, blocks);
  if (blocks.empty()) return;
  const ScopeNameSet kNames = ClockingSignalScope(unit_, decl);
  ProceduralOnlyHeads heads{{}, class_var_names_, auto_task_func_names_};
  for (const auto& [name, info] : var_array_info_) {
    if (info.is_dynamic || info.is_assoc || info.is_queue) {
      heads.dynamic_arrays.insert(name);
    }
  }
  for (const ModuleItem* block : blocks) {
    ReportUndeclaredClockingEvent(block, kNames, diag_);
    for (const auto& sig : block->clocking_signals) {
      if (sig.hier_expr == nullptr && !kNames.Contains(sig.name)) {
        diag_.Error(block->loc,
                    std::format("clocking signal '{}' names no net or "
                                "variable in the scope enclosing the "
                                "clocking block",
                                sig.name),
                    Subclause("14.3"));
      }
      if (DesignatesProceduralOnly(sig.hier_expr, heads)) {
        diag_.Error(block->loc,
                    std::format("clocking signal '{}' designates a variable "
                                "that only procedural code may reference",
                                sig.name),
                    Subclause("14.3"));
      }
    }
  }
}

}  // namespace delta
