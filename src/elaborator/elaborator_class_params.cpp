#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/dollar_contexts.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_items_params.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "elaborator/unit_aggregate_params.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

struct ClassParamRegistration {
  const ClassDecl* cls;
  std::unordered_set<std::string_view> formals;
  std::string_view key_prefix;
  std::string_view type_scope;
  ScopeMap values;
  ScopeMap& cu_param_scope;
  Arena& arena;
  DiagEngine& diag;
  const std::unordered_set<std::string_view>* specparams = nullptr;
};

static bool TakesRealClassParamValue(const Expr* pexpr, const DataType& type) {
  if (IsRealType(type.kind)) return true;
  bool untyped = type.kind == DataTypeKind::kImplicit && !type.is_signed &&
                 type.packed_dim_left == nullptr;
  return untyped && HasRealOperand(pexpr);
}

static std::optional<int64_t> FoldClassParamInteger(const Expr* pexpr,
                                                    const DataType& type,
                                                    const ScopeMap& values) {
  if (auto rounded = FoldRealValueAsInteger(pexpr, values)) return rounded;
  return FoldDeclaredParamValue(pexpr, type, values);
}

static bool IsNullLiteral(const Expr* e) {
  return e->kind == ExprKind::kIdentifier && e->text == "null";
}

static bool PatternItemsConstant(const Expr* e, const ScopeMap& values) {
  if (e->kind != ExprKind::kAssignmentPattern)
    return IsNullLiteral(e) || ConstEvalInt(e, values).has_value() ||
           ConstEvalReal(e, values).has_value();
  return std::ranges::all_of(e->elements, [&values](const Expr* item) {
    return PatternItemsConstant(item, values);
  });
}

static bool MentionsFormalOrSpecparam(const Expr* pexpr,
                                      const ClassParamRegistration& reg) {
  if (reg.specparams != nullptr && ExprMentionsAny(pexpr, *reg.specparams))
    return true;
  return ExprMentionsAny(pexpr, reg.formals);
}

static void ReportNonConstantClassParam(std::string_view pname,
                                        const Expr* pexpr,
                                        ClassParamRegistration& reg) {
  if (MentionsFormalOrSpecparam(pexpr, reg)) return;
  reg.diag.Error(pexpr->range.start,
                 std::format("class parameter '{}' value is not a constant "
                             "expression",
                             pname),
                 Subclause("6.20.2"));
}

static void RecordClassParam(std::string_view pname, const Expr* pexpr,
                             const DataType& type,
                             const std::vector<Expr*>& dims,
                             ClassParamRegistration& reg) {
  if (!pexpr || ContainsDollar(pexpr)) return;
  bool is_array = !dims.empty() || pexpr->kind == ExprKind::kAssignmentPattern;
  bool is_real = !is_array && TakesRealClassParamValue(pexpr, type);
  std::optional<int64_t> val;
  if (!is_real && !is_array)
    val = FoldClassParamInteger(pexpr, type, reg.values);
  bool constant = is_array  ? pexpr->kind != ExprKind::kAssignmentPattern ||
                                  PatternItemsConstant(pexpr, reg.values)
                  : is_real ? ConstEvalReal(pexpr, reg.values).has_value()
                            : val.has_value() || IsNullLiteral(pexpr);
  if (!constant) {
    ReportNonConstantClassParam(pname, pexpr, reg);
    return;
  }
  RegisterUnitAggregateParam(
      {reg.key_prefix, pname, pexpr, type, dims, reg.values});
  if (is_array || is_real || !val) return;
  auto* qname = reg.arena.Create<std::string>(std::string(reg.key_prefix) +
                                              "." + std::string(pname));
  reg.cu_param_scope[*qname] = *val;
  reg.values[pname] = *val;
  auto reading = TwoStateReading(pexpr, type, reg.values, *val);
  SetTwoStateReading(reg.values, pname, reading);
  SetTwoStateReading(reg.cu_param_scope, *qname, reading);
}

static const std::vector<Expr*>& PortParamDims(const ClassDecl& cls,
                                               std::string_view pname) {
  static const std::vector<Expr*> kNoDims;
  auto it = cls.param_port_unpacked_dims.find(pname);
  return it != cls.param_port_unpacked_dims.end() ? it->second : kNoDims;
}

static void RegisterOneClassParams(ClassParamRegistration& reg) {
  static const DataType kUntyped;
  UnitNamePrefixGuard prefix_guard(reg.key_prefix);
  const auto& params = reg.cls->params;
  const auto& types = reg.cls->param_types;
  for (size_t i = 0; i < params.size(); ++i) {
    const auto& [pname, pexpr] = params[i];
    if (reg.cls->type_param_names.count(pname)) continue;
    RecordClassParam(pname, pexpr, i < types.size() ? types[i] : kUntyped,
                     PortParamDims(*reg.cls, pname), reg);
  }
  for (const auto* m : reg.cls->members) {
    if (m->kind != ClassMemberKind::kProperty || !m->is_param) continue;
    DataType type = InClassScope(m->data_type, *reg.cls, reg.type_scope);
    RecordClassParam(m->name, m->init_expr, type, m->unpacked_dims, reg);
  }
}

static void RegisterClassTreeParams(ClassParamRegistration& reg) {
  RegisterOneClassParams(reg);
  for (const auto* m : reg.cls->members) {
    if (m->kind != ClassMemberKind::kClassDecl) continue;
    const ClassDecl* inner = m->nested_class;
    auto* prefix = reg.arena.Create<std::string>(
        std::string(reg.key_prefix) + "." + std::string(inner->name));
    auto* scope = reg.arena.Create<std::string>(
        std::string(reg.type_scope) + "::" + std::string(inner->name));
    ClassParamRegistration nested{
        inner,         ClassParamNames(inner), *prefix,   *scope,
        reg.values,    reg.cu_param_scope,     reg.arena, reg.diag,
        reg.specparams};
    RegisterClassTreeParams(nested);
  }
}

void RegisterClassParams(CompilationUnit* unit, ScopeMap& cu_param_scope,
                         Arena& arena, DiagEngine& diag) {
  for (auto* cls : unit->classes) {
    ClassParamRegistration reg{cls,
                               ClassParamNames(cls),
                               cls->name,
                               cls->name,
                               cu_param_scope,
                               cu_param_scope,
                               arena,
                               diag};
    RegisterClassTreeParams(reg);
  }
}

void RegisterModuleClassParams(const ClassDecl* cls,
                               const ModuleClassScope& module_scope,
                               ScopeMap& cu_param_scope, Arena& arena,
                               DiagEngine& diag) {
  ClassParamRegistration reg{cls,
                             ClassParamNames(cls),
                             cls->name,
                             cls->name,
                             module_scope.values,
                             cu_param_scope,
                             arena,
                             diag,
                             &module_scope.specparams};
  RegisterClassTreeParams(reg);
}

bool ExprMentionsAny(const Expr* e,
                     const std::unordered_set<std::string_view>& names) {
  if (!e) return false;
  if (!e->text.empty() && names.count(e->text)) return true;
  if (!e->callee.empty() && names.count(e->callee)) return true;
  for (const Expr* child :
       {e->lhs, e->rhs, e->condition, e->true_expr, e->false_expr, e->base,
        e->index, e->index_end, e->with_expr, e->stream_range}) {
    if (ExprMentionsAny(child, names)) return true;
  }
  for (const Expr* arg : e->args) {
    if (ExprMentionsAny(arg, names)) return true;
  }
  for (const Expr* elem : e->elements) {
    if (ExprMentionsAny(elem, names)) return true;
  }
  return false;
}

static bool NamesUnboundedParam(const Expr* e) {
  if (e->kind != ExprKind::kIdentifier) return false;
  const RtlirParamDecl* pd = RegisteredParamNamed(e->text);
  return pd != nullptr && pd->is_unbounded;
}

std::unordered_set<std::string_view> NonIntegralParamNames(
    const std::vector<ModuleItem*>* items, const ScopeMap& values) {
  std::unordered_set<std::string_view> names;
  if (items == nullptr) return names;
  for (const auto* item : *items) {
    if (item == nullptr || item->kind != ModuleItemKind::kParamDecl) continue;
    const Expr* v = item->init_expr;
    if (v == nullptr) continue;
    bool names_one = v->kind == ExprKind::kIdentifier && names.count(v->text);
    bool is_real = HasRealOperand(v) && ConstEvalReal(v, values);
    if (IsLoneDollar(v) || names_one || is_real) names.insert(item->name);
  }
  return names;
}

bool IsConstantClassParamValue(const Expr* e, const ScopeMap& scope) {
  if (e->kind == ExprKind::kAssignmentPattern)
    return PatternItemsConstant(e, scope);
  return ContainsDollar(e) || NamesUnboundedParam(e) ||
         ConstEvalInt(e, scope) || ConstEvalReal(e, scope);
}

std::unordered_set<std::string_view> ClassParamNames(const ClassDecl* cls) {
  std::unordered_set<std::string_view> names = cls->type_param_names;
  for (const auto& [pname, pexpr] : cls->params) names.insert(pname);
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kProperty && m->is_param)
      names.insert(m->name);
  }
  return names;
}

}  // namespace delta
