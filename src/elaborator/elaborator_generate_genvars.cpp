#include <format>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_items_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

using GenvarSet = std::unordered_set<std::string_view>;

void CheckGenvarsInScope(const std::vector<ModuleItem*>& items,
                         GenvarSet genvars, DiagEngine& diag);

void CheckLoopGenvar(const ModuleItem* item, GenvarSet genvars,
                     DiagEngine& diag) {
  const Stmt* init = item->gen_init;
  std::string_view index = init->lhs->text;
  if (!init->var_name.empty()) {
    genvars.insert(init->var_name);
  } else if (!index.empty() && !genvars.contains(index)) {
    diag.Error(item->loc,
               std::format("loop generate index '{}' is declared by no genvar "
                           "declaration before the loop",
                           index),
               Subclause("27.4"));
  }
  CheckGenvarsInScope(item->gen_body, std::move(genvars), diag);
}

void CheckConstructGenvars(const ModuleItem* item, const GenvarSet& genvars,
                           DiagEngine& diag) {
  if (item->kind == ModuleItemKind::kGenerateFor) {
    CheckLoopGenvar(item, genvars, diag);
    return;
  }
  CheckGenvarsInScope(item->gen_body, genvars, diag);
  for (const auto& ci : item->gen_case_items) {
    CheckGenvarsInScope(ci.body, genvars, diag);
  }
  if (item->gen_else != nullptr) {
    CheckConstructGenvars(item->gen_else, genvars, diag);
  }
}

void CheckGenvarsInScope(const std::vector<ModuleItem*>& items,
                         GenvarSet genvars, DiagEngine& diag) {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kGenerateFor ||
        IsConditionalGenerateConstruct(item->kind)) {
      CheckConstructGenvars(item, genvars, diag);
    } else if (item->is_genvar) {
      genvars.insert(item->name);
    } else {
      genvars.erase(item->name);
    }
  }
}

}  // namespace

void ReportUndeclaredLoopGenvars(const ModuleDecl* decl, DiagEngine& diag) {
  CheckGenvarsInScope(decl->items, {}, diag);
}

}  // namespace delta
