#include "elaborator/checker_instance_assertion.h"

#include <unordered_map>

#include "common/arena.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/property_instance.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

static void TakeFormalActualClock(ModuleItem* copy, const ModuleItem* item,
                                  const ActualsByFormal& actuals,
                                  const PropertyRegistry& registry,
                                  Arena& arena) {
  if (!copy->sensitivity.empty() || copy->body == nullptr) return;
  copy->sensitivity =
      FormalOpeningClock(copy->body->assert_property, actuals, registry, arena);
  if (copy->sensitivity.empty()) return;
  if (copy->body == item->body) copy->body = arena.Create<Stmt>(*item->body);
  copy->body->assert_clock_from_actual = true;
}

ModuleItem* CheckerInstanceAssertion(
    ModuleItem* item, const RtlirModule* mod,
    const std::unordered_map<const RtlirModule*, ActualsByFormal>& trees,
    const PropertyRegistry& registry, Arena& arena) {
  auto found = trees.find(mod);
  if (found == trees.end() || found->second.empty()) return item;
  const ActualsByFormal& actuals = found->second;
  auto* copy = arena.Create<ModuleItem>(*item);
  const Stmt* stmt = item->body;
  const Expr* spec = stmt != nullptr ? stmt->assert_expr : item->assert_expr;
  bool names_formal = (stmt == nullptr || (stmt->assert_property == nullptr &&
                                           stmt->assert_sequence == nullptr)) &&
                      spec != nullptr && spec->kind == ExprKind::kIdentifier &&
                      actuals.contains(spec->text);
  if (names_formal) {
    if (stmt == nullptr) {
      copy->prop_instance_name = {};
      SubstituteBooleanSpec(copy, arena);
    } else {
      copy->body = arena.Create<Stmt>(*stmt);
    }
    copy->body->assert_property = arena.Create<PropertyExprNode>();
    copy->body->assert_property->boolean = copy->body->assert_expr;
  }
  TakeFormalActualClock(copy, item, actuals, registry, arena);
  return copy;
}

}  // namespace delta
