#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>

#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator_items_params.h"
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
                                                     const DataType& type,
                                                     const ScopeMap& values) {
  if (pexpr == nullptr) return std::nullopt;
  auto v = FoldParamValueRoundingReal(pexpr, type, values);
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
  return {false, FoldClassParamDefault(pexpr, decl->param_types[i], values)};
}

struct SpecializedTarget {
  SpecializationArg arg;
  const Expr* source = nullptr;
  DataType type;
  ScopeMap scope;
};

static std::optional<double> HeldAs(const DataType& type,
                                    std::optional<double> value) {
  if (type.kind != DataTypeKind::kShortreal) return value;
  return value.transform(
      [](double v) { return static_cast<double>(static_cast<float>(v)); });
}

static void BindReal(std::string_view name, const BoundSource& from) {
  if (!HoldsRealValue(*from.type, from.source)) return;
  std::optional<double> value =
      HeldAs(*from.type, ConstEvalReal(from.source, from.source_scope));
  if (value) SetConstFuncRealLocal(name, *value);
}

static void BindString(std::string_view name, const BoundSource& from) {
  if (from.type->kind != DataTypeKind::kString) return;
  std::optional<std::string> chars =
      ConstEvalString(from.source, from.source_scope);
  if (chars) SetConstFuncStringLocal(name, std::move(*chars));
}

class SpecializationWalk {
 public:
  SpecializationWalk(const Expr* expr, const ClassDecl* decl,
                     const ScopeMap& scope)
      : expr_(expr), decl_(decl), scope_(scope), values_(scope) {}

  std::optional<SpecializedTarget> Find() {
    std::string_view target = expr_->rhs->text;
    for (size_t i = 0; i < decl_->params.size(); ++i) {
      std::string_view pname = decl_->params[i].first;
      if (decl_->type_param_names.count(pname) != 0) continue;
      SpecializationArg arg = HeaderParamArg(expr_, decl_, i, scope_, values_);
      const Expr* actual = WrittenParamActual(*expr_->lhs, pname, i);
      const DataType& type = decl_->param_types[i];
      BoundSource from =
          actual != nullptr
              ? BoundSource{actual, &type, scope_}
              : BoundSource{decl_->params[i].second, &type, values_};
      if (pname == target)
        return SpecializedTarget{Answer(arg), from.source, type,
                                 from.source_scope};
      Take(pname, arg.value, from);
    }
    for (const auto* m : decl_->members) {
      if (m->kind != ClassMemberKind::kProperty || !m->is_param) continue;
      DataType type = InClassScope(m->data_type, *decl_);
      auto v = FoldClassParamDefault(m->init_expr, type, values_);
      if (m->name == target)
        return SpecializedTarget{Answer({false, v}), m->init_expr,
                                 std::move(type), values_};
      Take(m->name, v, {m->init_expr, &type, values_});
    }
    return std::nullopt;
  }

 private:
  void Take(std::string_view name, const std::optional<ConstVal>& v,
            const BoundSource& from) {
    DeclareLocalName(name);
    BindReal(name, from);
    BindString(name, from);
    Bind(values_, name, v, from);
  }

  const Expr* expr_;
  const ClassDecl* decl_;
  const ScopeMap& scope_;
  ScopeMap values_;
};

SpecializationArg ConstEvalSpecializedClassParam(const Expr* expr,
                                                 const ScopeMap& scope) {
  const ClassDecl* decl = SpecializedParamClass(expr);
  if (!decl) return {};
  LocalNameFrame frame;
  std::optional<SpecializedTarget> target =
      SpecializationWalk(expr, decl, scope).Find();
  return target ? target->arg : SpecializationArg{};
}

bool NamesSpecializedClassParam(const Expr* expr) {
  return SpecializedParamClass(expr) != nullptr;
}

std::optional<double> ConstEvalSpecializedClassParamReal(
    const Expr* expr, const ScopeMap& scope) {
  LocalNameFrame frame;
  std::optional<SpecializedTarget> target =
      SpecializationWalk(expr, SpecializedParamClass(expr), scope).Find();
  if (!target) return std::nullopt;
  if (!HoldsRealValue(target->type, target->source))
    return target->arg.value.transform(
        [](const ConstVal& v) { return static_cast<double>(v.value); });
  return HeldAs(target->type, ConstEvalReal(target->source, target->scope));
}

std::optional<std::string> ConstEvalSpecializedClassParamString(
    const Expr* expr, const ScopeMap& scope) {
  LocalNameFrame frame;
  std::optional<SpecializedTarget> target =
      SpecializationWalk(expr, SpecializedParamClass(expr), scope).Find();
  if (!target) return std::nullopt;
  return ConstEvalString(target->source, target->scope);
}

}  // namespace delta
