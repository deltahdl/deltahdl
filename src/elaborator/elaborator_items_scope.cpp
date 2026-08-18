#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

ScopeMap Elaborator::BuildParamScope(const RtlirModule* mod) const {
  return BuildParamScope(mod, gen_prefix_scopes_);
}

ScopeMap Elaborator::BuildParamScope(
    const RtlirModule* mod, const std::vector<std::string_view>& scopes) const {
  ScopeMap scope = cu_param_scope_;
  // §3.12.1: an explicit $unit:: prefix names the compilation-unit-scope
  // declaration and exists precisely so a same-named module-local declaration
  // cannot shadow it. Expose each compilation-unit-scope parameter a second
  // time under a "$unit::"-qualified key, which the local-parameter overlay
  // below never overwrites, so a $unit:: reference keeps resolving to the
  // outermost value.
  for (const auto& [name, val] : cu_param_scope_) {
    if (name.find('.') != std::string_view::npos) continue;
    auto* key = arena_.Create<std::string>("$unit::" + std::string(name));
    scope[*key] = val;
  }
  // §23.9 makes a generate block "a new scope", so a parameter one declares is
  // read only by an expression written in that block or in one nested inside
  // it. Entering it under its bare name for every expression in the module
  // would fold it into expressions that cannot name it at all.
  for (const auto& p : mod->params) {
    if (!p.is_resolved) continue;
    if (!ParamVisibleFromScopes(p.gen_block_prefix, scopes)) continue;
    scope[p.name] = p.resolved_value;
  }
  return scope;
}

bool Elaborator::RefersToUnboundedParam(const RtlirModule* mod,
                                        std::string_view name) const {
  for (const auto& p : mod->params) {
    if (!p.is_unbounded || p.name != name) continue;
    // §23.9: an unbounded parameter a generate block declares is not what a
    // reference outside that block names, so it must not make the parameter
    // that reference initialises unbounded in its turn.
    if (ParamVisibleFromScopes(p.gen_block_prefix, gen_prefix_scopes_)) {
      return true;
    }
  }
  return false;
}

namespace {

bool ExprContainsDollarSubexpr(const Expr* e);

// Returns true if any of the fixed scalar child-expression pointers of `e`
// contains a self-contained `$` subexpression. Factored out of the recursive
// walk so the driver stays below the cognitive-complexity threshold.
bool AnyScalarChildContainsDollar(const Expr* e) {
  const Expr* const kChildren[] = {
      e->lhs,  e->rhs,   e->condition, e->true_expr, e->false_expr,
      e->base, e->index, e->index_end, e->with_expr, e->repeat_count};
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
