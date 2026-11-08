#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>
#include <unordered_map>

#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

static const std::unordered_map<std::string_view, const ClassDecl*>*
    g_param_class_registry = nullptr;

ParamClassRegistryGuard::ParamClassRegistryGuard(
    const std::unordered_map<std::string_view, const ClassDecl*>* classes)
    : prev_(g_param_class_registry) {
  g_param_class_registry = classes;
}

ParamClassRegistryGuard::~ParamClassRegistryGuard() {
  g_param_class_registry = prev_;
}

static const ClassDecl* SpecializedParamClass(const Expr* expr) {
  if (!g_param_class_registry) return nullptr;
  const Expr* base = expr->lhs;
  if (!base || base->kind != ExprKind::kIdentifier || !base->has_param_spec ||
      base->elements.empty())
    return nullptr;
  if (!expr->rhs || expr->rhs->kind != ExprKind::kIdentifier) return nullptr;
  auto cit = g_param_class_registry->find(base->text);
  if (cit == g_param_class_registry->end()) return nullptr;
  return cit->second;
}

static SpecializationArg NamedParamOverride(const Expr& base,
                                            std::string_view name,
                                            const ScopeMap& scope) {
  const auto& elems = base.elements;
  const auto& names = base.arg_names;
  for (size_t j = 0; j < elems.size(); ++j) {
    if (j < names.size() && !names[j].empty() && names[j] == name && elems[j])
      return {true, ConstEvalFull(elems[j], scope)};
  }
  return {};
}

static const Expr* WrittenParamActual(const Expr& base, std::string_view pname,
                                      size_t pos) {
  const auto& elems = base.elements;
  const auto& names = base.arg_names;
  for (size_t j = 0; j < elems.size(); ++j) {
    if (j < names.size() && names[j] == pname) return elems[j];
  }
  bool ordered = names.empty() || (pos < names.size() && names[pos].empty());
  return ordered && pos < elems.size() ? elems[pos] : nullptr;
}

static SpecializationArg OrderedParamOverride(const Expr& base, size_t pos,
                                              const ScopeMap& scope) {
  const auto& elems = base.elements;
  const auto& names = base.arg_names;
  bool ordered = names.empty() || (pos < names.size() && names[pos].empty());
  if (ordered && pos < elems.size() && elems[pos])
    return {true, ConstEvalFull(elems[pos], scope)};
  return {};
}

static std::optional<ConstVal> FoldClassParamDefault(const Expr* pexpr,
                                                     const DataType* type,
                                                     const ScopeMap& values) {
  if (pexpr == nullptr) return std::nullopt;
  auto v = type != nullptr ? FoldDeclaredParamValue(pexpr, *type, values)
                           : ConstEvalInt(pexpr, values);
  if (!v) return std::nullopt;
  return ConstVal{*v, 32, true};
}

struct BoundSource {
  const Expr* source;
  const DataType* type;
  const ScopeMap& source_scope;
};

static void Bind(ScopeMap& values, std::string_view name,
                 const std::optional<ConstVal>& v, const BoundSource& from) {
  if (v) {
    values[name] = v->value;
  } else {
    values.erase(name);
  }
  std::optional<int64_t> reading;
  if (v && from.source != nullptr && from.type != nullptr)
    reading =
        TwoStateReading(from.source, *from.type, from.source_scope, v->value);
  SetTwoStateReading(values, name, reading);
}

static SpecializationArg Answer(const SpecializationArg& arg) {
  if (arg.supplied || arg.value) return {true, arg.value};
  return {};
}

static SpecializationArg HeaderParamArg(const Expr* expr, const ClassDecl* decl,
                                        size_t i, const ScopeMap& scope,
                                        const ScopeMap& values) {
  const auto& [pname, pexpr] = decl->params[i];
  SpecializationArg arg = NamedParamOverride(*expr->lhs, pname, scope);
  if (!arg.supplied) arg = OrderedParamOverride(*expr->lhs, i, scope);
  if (arg.supplied) return arg;
  const DataType* type =
      i < decl->param_types.size() ? &decl->param_types[i] : nullptr;
  return {false, FoldClassParamDefault(pexpr, type, values)};
}

static SpecializationArg FoldUnderSpecialization(const Expr* expr,
                                                 const ClassDecl* decl,
                                                 const ScopeMap& scope) {
  std::string_view target = expr->rhs->text;
  ScopeMap values = scope;
  for (size_t i = 0; i < decl->params.size(); ++i) {
    std::string_view pname = decl->params[i].first;
    if (decl->type_param_names.count(pname) != 0) continue;
    SpecializationArg arg = HeaderParamArg(expr, decl, i, scope, values);
    if (pname == target) return Answer(arg);
    const Expr* actual = WrittenParamActual(*expr->lhs, pname, i);
    const DataType* type =
        i < decl->param_types.size() ? &decl->param_types[i] : nullptr;
    Bind(values, pname, arg.value,
         actual != nullptr ? BoundSource{actual, type, scope}
                           : BoundSource{decl->params[i].second, type, values});
  }
  for (const auto* m : decl->members) {
    if (m->kind != ClassMemberKind::kProperty || !m->is_param) continue;
    DataType type = InClassScope(m->data_type, *decl);
    auto v = FoldClassParamDefault(m->init_expr, &type, values);
    if (m->name == target) return Answer({false, v});
    Bind(values, m->name, v, {m->init_expr, &type, values});
  }
  return {};
}

SpecializationArg ConstEvalSpecializedClassParam(const Expr* expr,
                                                 const ScopeMap& scope) {
  const ClassDecl* decl = SpecializedParamClass(expr);
  if (!decl) return {};
  return FoldUnderSpecialization(expr, decl, scope);
}

}  // namespace delta
