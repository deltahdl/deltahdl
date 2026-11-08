#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <optional>
#include <string>
#include <string_view>

#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator_items_params.h"
#include "elaborator/rtlir.h"
#include "elaborator/typename_writer.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

const RtlirVariable* RegisteredVariable(std::string_view name) {
  const RtlirModule* mod = RegisteredModule();
  if (mod == nullptr) return nullptr;
  for (const RtlirVariable& var : mod->variables) {
    if (var.name == name) return &var;
  }
  return nullptr;
}

uint32_t PackedElementWidth(const RtlirVariable& var) {
  const DataType* type = var.written_type;
  while (type != nullptr && type->kind == DataTypeKind::kNamed &&
         type->scope_name.empty() && type->packed_dim_left == nullptr) {
    type = RegisteredTypedef(type->type_name);
  }
  if (type == nullptr || type->packed_dim_left == nullptr) return 1;
  ScopeMap scope = RegisteredModuleScope();
  std::optional<int64_t> left = ConstEvalInt(type->packed_dim_left, scope);
  std::optional<int64_t> right = ConstEvalInt(type->packed_dim_right, scope);
  if (!left || !right) return 1;
  auto span = static_cast<uint32_t>(std::abs(*left - *right) + 1);
  return std::max<uint32_t>(var.width / span, 1);
}

TypenameEnvironment ElabTypenameEnvironment(bool& declined) {
  TypenameEnvironment env;
  env.value_of = [&declined](const Expr* expr) {
    std::optional<int64_t> value = ConstEvalInt(expr, RegisteredModuleScope());
    if (!value) declined = true;
    return value.value_or(0);
  };
  env.resolve_name = [](std::string_view scope_name, std::string_view type_name,
                        std::string&) {
    return scope_name.empty() ? RegisteredTypedef(type_name) : nullptr;
  };
  env.qualified_class_name = [&declined](std::string_view, std::string_view) {
    declined = true;
    return std::string();
  };
  env.scope_name = [&declined]() -> std::string_view {
    const RtlirModule* mod = RegisteredModule();
    if (mod == nullptr) {
      declined = true;
      return {};
    }
    return mod->name;
  };
  env.width_of = [](const DataType& type) {
    return RegisteredTypeWidth(type, RegisteredModuleScope());
  };
  env.name_self_type = [](std::string_view name) -> SelfType {
    const RtlirVariable* var = RegisteredVariable(name);
    if (var == nullptr || var->is_real || var->is_string ||
        var->num_unpacked_dims != 0) {
      return {};
    }
    return {var->width, var->is_signed, var->is_4state, true};
  };
  env.is_real = [](const Expr* expr) { return HasRealOperand(expr); };
  env.element_width = [](std::string_view name) -> uint32_t {
    const RtlirVariable* var = RegisteredVariable(name);
    return var == nullptr ? 1 : PackedElementWidth(*var);
  };
  return env;
}

std::string TypenameOfDeclaredName(std::string_view name,
                                   TypenameWriter& writer) {
  if (const RtlirVariable* var = RegisteredVariable(name)) {
    if (var->written_type == nullptr) return {};
    return writer.OfType(*var->written_type, "", name) + UnpackedDimsText(*var);
  }
  if (RegisteredTypedef(name) == nullptr) return {};
  DataType reference;
  reference.kind = DataTypeKind::kNamed;
  reference.type_name = name;
  return writer.OfType(reference, "", name);
}

std::string TypenameOfElement(const Expr* arg, TypenameWriter& writer) {
  if (arg->kind != ExprKind::kSelect || arg->index_end != nullptr ||
      arg->base->kind != ExprKind::kIdentifier) {
    return {};
  }
  std::string_view name = arg->base->text;
  const RtlirVariable* var = RegisteredVariable(name);
  if (var == nullptr || var->written_type == nullptr) return {};
  std::string unpacked = UnpackedDimsText(*var);
  if (unpacked.empty()) return {};
  return writer.OfType(*var->written_type, "", name) +
         ElementDimsText(unpacked);
}

std::string TypenameOfArgument(const Expr* arg, TypenameWriter& writer,
                               const TypenameEnvironment& env) {
  if (arg->kind == ExprKind::kTypeRef) {
    return arg->type_value == nullptr
               ? std::string()
               : writer.OfType(*arg->type_value, "", "type");
  }
  if (std::optional<DataType> keyword = KeywordTypeOf(arg)) {
    return writer.OfType(*keyword, "", "type");
  }
  if (arg->kind == ExprKind::kIdentifier) {
    return TypenameOfDeclaredName(arg->text, writer);
  }
  std::string element = TypenameOfElement(arg, writer);
  return element.empty() ? TypenameOfOperation(arg, env) : element;
}

}  // namespace

std::optional<std::string> ConstTypenameChars(const Expr* expr) {
  if (expr->callee != "$typename" || expr->args.size() != 1) {
    return std::nullopt;
  }
  bool declined = false;
  TypenameEnvironment env = ElabTypenameEnvironment(declined);
  TypenameWriter writer(env);
  std::string text = TypenameOfArgument(expr->args[0], writer, env);
  if (text.empty() || declined) return std::nullopt;
  return text;
}

}  // namespace delta
