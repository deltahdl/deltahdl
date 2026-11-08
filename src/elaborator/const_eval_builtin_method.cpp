#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_enum_member.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_expr.h"

namespace delta {
namespace {

constexpr std::array<std::string_view, 53> kBuiltinMethodNames = {
    "len",        "putc",
    "getc",       "toupper",
    "tolower",    "compare",
    "icompare",   "substr",
    "atoi",       "atohex",
    "atooct",     "atobin",
    "atoreal",    "itoa",
    "hextoa",     "octtoa",
    "bintoa",     "realtoa",
    "first",      "last",
    "next",       "prev",
    "num",        "name",
    "size",       "delete",
    "exists",     "insert",
    "pop_front",  "pop_back",
    "push_front", "push_back",
    "find",       "find_index",
    "find_first", "find_first_index",
    "find_last",  "find_last_index",
    "min",        "max",
    "unique",     "unique_index",
    "reverse",    "sort",
    "rsort",      "shuffle",
    "sum",        "product",
    "and",        "or",
    "xor",        "index",
    "map"};

bool IsBuiltinMethodName(std::string_view method) {
  return std::ranges::find(kBuiltinMethodNames, method) !=
         kBuiltinMethodNames.end();
}

}  // namespace

const Expr* BuiltinMethodMember(const Expr* expr) {
  if (!expr) return nullptr;
  const Expr* member = nullptr;
  if (expr->kind == ExprKind::kCall && expr->lhs &&
      expr->lhs->kind == ExprKind::kMemberAccess) {
    member = expr->lhs;
  } else if (expr->kind == ExprKind::kMemberAccess) {
    member = expr;
  } else {
    return nullptr;
  }
  if (member->is_scope_resolution || !member->rhs ||
      member->rhs->kind != ExprKind::kIdentifier)
    return nullptr;
  if (!IsBuiltinMethodName(member->rhs->text)) return nullptr;
  return member;
}

namespace {

const RtlirVariable* RegisteredVariable(std::string_view name) {
  const RtlirModule* mod = RegisteredModule();
  if (!mod) return nullptr;
  for (const auto& var : mod->variables) {
    if (var.name == name) return &var;
  }
  return nullptr;
}

const std::vector<RtlirEnumMember>* EnumMembers(const Expr* operand) {
  if (!operand || operand->kind != ExprKind::kIdentifier) return nullptr;
  const RtlirVariable* var = RegisteredVariable(operand->text);
  if (!var || var->enum_type_name.empty()) return nullptr;
  const RtlirModule* mod = RegisteredModule();
  auto it = mod->enum_types.find(var->enum_type_name);
  if (it == mod->enum_types.end()) return nullptr;
  return &it->second;
}

std::optional<std::string> StringParamValue(const Expr* operand,
                                            const ScopeMap& scope) {
  if (operand->kind != ExprKind::kIdentifier)
    return ConstEvalAggregatePartString(operand, scope);
  const RtlirModule* mod = RegisteredModule();
  if (!mod) return std::nullopt;
  for (const auto& param : mod->params) {
    if (param.name != operand->text) continue;
    if (!ParamVisibleFromScopes(param.gen_block_prefix,
                                RegisteredGenPrefixes()))
      continue;
    if (!param.is_string_value) return std::nullopt;
    return std::string(param.resolved_string);
  }
  return std::nullopt;
}

std::optional<ConstVal> StringParamChar(const Expr* call, std::string_view str,
                                        const ScopeMap& scope) {
  if (call->kind != ExprKind::kCall || call->args.size() != 1)
    return std::nullopt;
  auto index = ConstEvalInt(call->args[0], scope);
  if (!index) return std::nullopt;
  const bool kInside =
      *index >= 0 && static_cast<uint64_t>(*index) < str.size();
  const int64_t kCode =
      kInside ? static_cast<int8_t>(str[static_cast<size_t>(*index)]) : 0;
  return ConstVal{kCode, 8, true};
}

}  // namespace

std::optional<ConstVal> ConstEvalBuiltinMethodFull(const Expr* expr,
                                                   const ScopeMap& scope) {
  const Expr* member = BuiltinMethodMember(expr);
  if (!member) return std::nullopt;
  const std::string_view kMethod = member->rhs->text;
  if (kMethod == "getc") {
    auto str = StringParamValue(member->lhs, scope);
    if (!str) return std::nullopt;
    return StringParamChar(expr, *str, scope);
  }
  if (expr->kind == ExprKind::kCall && !expr->args.empty()) return std::nullopt;
  if (kMethod == "len") {
    auto str = StringParamValue(member->lhs, scope);
    if (!str) return std::nullopt;
    return ConstVal{static_cast<int64_t>(str->size()), 32, true};
  }
  const std::vector<RtlirEnumMember>* members = EnumMembers(member->lhs);
  if (members == nullptr) return std::nullopt;
  if (kMethod == "num")
    return ConstVal{static_cast<int64_t>(members->size()), 32, true};
  if (kMethod == "first") return ConstVal{members->front().value, 32, true};
  if (kMethod == "last") return ConstVal{members->back().value, 32, true};
  return std::nullopt;
}

std::optional<bool> BuiltinMethodCallIsConstant(const Expr* expr,
                                                const ScopeMap& scope) {
  if (!BuiltinMethodMember(expr)) return std::nullopt;
  if (!AllElementsConstant(expr->args, scope)) return false;
  return ConstEvalBuiltinMethodFull(expr, scope).has_value();
}

}  // namespace delta
