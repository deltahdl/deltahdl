#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "elaborator/unit_scope_order.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

ScopeMap Elaborator::BuildParamScope(const RtlirModule* mod) const {
  ScopeMap scope = BuildParamScope(mod, gen_prefix_scopes_);
  for (const auto& [name, value] : gen_loop_consts_)
    BindDeclaredConstant(scope, name, value);
  return scope;
}

ScopeMap Elaborator::BuildParamScope(
    const RtlirModule* mod, const std::vector<std::string_view>& scopes) const {
  ScopeMap scope = cu_param_scope_;
  for (const auto& [name, val] : cu_param_scope_) {
    if (name.find('.') != std::string_view::npos) continue;
    auto* key = arena_.Create<std::string>("$unit::" + std::string(name));
    scope[*key] = val;
  }
  for (const auto& entry : mod->enum_types) {
    for (const auto& member : entry.second)
      BindDeclaredConstant(scope, member.name, member.value);
  }
  for (const auto& [name, value] : mod->constant_formals)
    BindDeclaredConstant(scope, name, value);
  for (const auto& p : mod->params) {
    if (!p.is_resolved) continue;
    if (!ParamVisibleFromScopes(p.gen_block_prefix, scopes)) continue;
    BindDeclaredConstant(scope, p.name, p.resolved_value);
  }
  return scope;
}

bool Elaborator::RefersToUnboundedParam(const RtlirModule* mod,
                                        std::string_view name) const {
  for (const auto& p : mod->params) {
    if (!p.is_unbounded || p.name != name) continue;
    if (ParamVisibleFromScopes(p.gen_block_prefix, gen_prefix_scopes_)) {
      return true;
    }
  }
  return false;
}

namespace {

bool ExprContainsDollarSubexpr(const Expr* e);

bool AnyScalarChildContainsDollar(const Expr* e) {
  const Expr* const kChildren[] = {
      e->lhs,        e->rhs,          e->condition,   e->true_expr,
      e->false_expr, e->base,         e->index,       e->index_end,
      e->with_expr,  e->stream_range, e->repeat_count};
  for (const Expr* c : kChildren) {
    if (ExprContainsDollarSubexpr(c)) return true;
  }
  return false;
}

bool ExprContainsDollarSubexpr(const Expr* e) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier && e->text == "$") return true;
  if (AnyScalarChildContainsDollar(e)) return true;
  for (const Expr* a : e->args)
    if (ExprContainsDollarSubexpr(a)) return true;
  for (const Expr* el : e->elements)
    if (ExprContainsDollarSubexpr(el)) return true;
  return false;
}

}  // namespace

bool Elaborator::ContainsDollarSubexpr(const Expr* e) const {
  return ExprContainsDollarSubexpr(e);
}

bool Elaborator::DeclaresNetOrVariable(std::string_view name) const {
  return var_types_.count(name) != 0 || net_names_.count(name) != 0;
}

bool Elaborator::NamesNet(std::string_view name, SourceLoc loc) const {
  if (net_names_.count(name) != 0) return true;
  if (var_types_.count(name) != 0) return false;
  for (const ModuleDecl* decl : module_decl_path_) {
    if (ModuleDeclaresName(decl, name)) return false;
  }
  return UnitNetBefore(unit_, name, loc) != nullptr;
}

std::unordered_set<std::string_view> Elaborator::NetNamesAt(
    SourceLoc loc) const {
  std::unordered_set<std::string_view> names = net_names_;
  for (const ModuleItem* item : unit_->cu_items) {
    if (NamesNet(item->name, loc)) names.insert(item->name);
  }
  return names;
}

std::string_view Elaborator::ScopedName(std::string_view base) {
  if (gen_prefix_.empty()) return base;
  std::string full = gen_prefix_ + std::string(base);
  return {arena_.AllocString(full.c_str(), full.size()), full.size()};
}

std::string_view Elaborator::InternedGenPrefix() {
  if (gen_prefix_.empty()) return {};
  return {arena_.AllocString(gen_prefix_.c_str(), gen_prefix_.size()),
          gen_prefix_.size()};
}

}  // namespace delta
