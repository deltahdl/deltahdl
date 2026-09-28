#include <cstddef>
#include <optional>
#include <string_view>
#include <unordered_map>

#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

// §8.25.1: registry of parameterized-class declarations visible to the constant
// folder, installed by the elaborator via ParamClassRegistryGuard. Null unless
// a guard is live. Used to map an accessed value-parameter name to its port
// position when resolving a specialization override.
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

// The class declaration behind a `C#(args)::name` member access, or null when
// the access is not of that shape or names no registered parameterized class.
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

// A named override, `.name(value)`, anywhere in the specialization's argument
// list.
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

// An ordered override, the argument occupying the parameter's own port
// position. Only an argument list that is ordered at that position qualifies.
static SpecializationArg OrderedParamOverride(const Expr& base, size_t pos,
                                              const ScopeMap& scope) {
  const auto& elems = base.elements;
  const auto& names = base.arg_names;
  bool ordered = names.empty() || (pos < names.size() && names[pos].empty());
  if (ordered && pos < elems.size() && elems[pos])
    return {true, ConstEvalFull(elems[pos], scope)};
  return {};
}

// §6.20.2 with §11.6.1: a parameter's default folded as the right-hand side of
// an assignment to the declared `type` over `values`, as RecordClassParam
// (elaborator_class_params.cpp) folds the default it records under
// "Class.name".
static std::optional<ConstVal> FoldClassParamDefault(const Expr* pexpr,
                                                     const DataType* type,
                                                     const ScopeMap& values) {
  if (pexpr == nullptr) return std::nullopt;
  auto v = type != nullptr ? FoldDeclaredParamValue(pexpr, *type, values)
                           : ConstEvalInt(pexpr, values);
  if (!v) return std::nullopt;
  return ConstVal{*v, 32, true};
}

// The value `values` gives a parameter from what one fold answered: the
// value where it folded, and nothing where it did not, so that a name the
// caller's scope happens to hold is not read in its place.
static void Bind(ScopeMap& values, std::string_view name,
                 const std::optional<ConstVal>& v) {
  if (v) {
    values[name] = v->value;
  } else {
    values.erase(name);
  }
}

// What the walk below answers for the parameter it was looking for. `arg`
// holds an override where `supplied` is set, and otherwise the default folded
// under the specialization. An override decides the answer whether or not it
// folded (§8.25.1). A default that did not fold is left unanswered, so that
// the class's own "Class.name" entry, folded where the class was registered,
// answers instead.
static SpecializationArg Answer(const SpecializationArg& arg) {
  if (arg.supplied || arg.value) return {true, arg.value};
  return {};
}

// §8.25 gives each specialization its own parameter values, and §6.20.1 lets a
// parameter depend on earlier ones, a class body localparam on the header's.
// So the parameter `C#(args)::name` names is found by walking the class's
// value parameters in the order they are written: each takes its override
// where the list writes one, named or ordered, and otherwise its default
// folded over the values before it, and the body parameters follow. A
// default read straight from the class's own "Class.name" entry was folded
// over the class's defaults, so `C#(4)::N` of `localparam int N = W * 2` read
// the default `W = 8` and answered 16.
static SpecializationArg FoldUnderSpecialization(const Expr* expr,
                                                 const ClassDecl* decl,
                                                 const ScopeMap& scope) {
  std::string_view target = expr->rhs->text;
  ScopeMap values = scope;
  for (size_t i = 0; i < decl->params.size(); ++i) {
    std::string_view pname = decl->params[i].first;
    if (decl->type_param_names.count(pname) != 0) continue;
    SpecializationArg arg = NamedParamOverride(*expr->lhs, pname, scope);
    if (!arg.supplied) arg = OrderedParamOverride(*expr->lhs, i, scope);
    if (!arg.supplied) {
      const DataType* type =
          i < decl->param_types.size() ? &decl->param_types[i] : nullptr;
      arg = {arg.supplied,
             FoldClassParamDefault(decl->params[i].second, type, values)};
    }
    if (pname == target) return Answer(arg);
    Bind(values, pname, arg.value);
  }
  for (const auto* m : decl->members) {
    if (m->kind != ClassMemberKind::kProperty || !m->is_param) continue;
    auto v = FoldClassParamDefault(m->init_expr, &m->data_type, values);
    if (m->name == target) return Answer({false, v});
    Bind(values, m->name, v);
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
