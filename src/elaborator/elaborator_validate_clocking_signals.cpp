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
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

// What a clocking item names (§14.3, printed page 355), the value a cycle
// delay may take (§14.11, printed page 361), and the declarations a nested
// declaration sits in, which §14.12 (printed page 362) carries a default
// clocking into.

namespace delta {

// Whether `scope`, or a declaration nested in it, holds `decl`; when it does,
// the declarations from the one holding `decl` out to `scope` are appended to
// `path`, innermost first.
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

// Reports each cycle delay under `s` whose count folds to a negative constant,
// on a `##` statement and on a synchronous drive alike, both of which keep the
// count in Stmt::cycle_delay.
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

// The clocking blocks among `items`, those of the generate blocks they hold
// included.
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

// The names §6.21 (printed page 134) limits to procedural code when one is
// the head of a select or of a member access: a dynamically sized array, a
// queue or an associative array, whose elements are referenced only there; a
// class variable, whose object's members are; and an automatic task or
// function, whose variables are.
struct ProceduralOnlyHeads {
  std::unordered_set<std::string_view> dynamic_arrays;
  const std::unordered_set<std::string_view>& class_vars;
  const std::unordered_set<std::string_view>& auto_subroutines;
};

bool IsIdentIn(const Expr* e, const std::unordered_set<std::string_view>& set) {
  return e != nullptr && e->kind == ExprKind::kIdentifier &&
         set.contains(e->text);
}

// Whether `e` references a variable §6.21 limits to procedural code.
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

// The names a clocking item may name in `decl`: what `decl` declares, what
// each declaration enclosing it declares (§23.4), and what the compilation
// unit's scope and its packages declare (§3.12.1, §26.3). ScopeNameSet holds
// more than any one scope declares, so it only ever leaves a name unreported.
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

}  // namespace

// §14.3 (printed page 355): a clocking item written without an expression
// names a net or variable of the scope enclosing the clocking block, and no
// clocking signal designates a variable §6.21 restricts to a procedural block.
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
