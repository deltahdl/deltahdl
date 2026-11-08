#include "elaborator/scope_value_type.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/expression_self_type.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "elaborator/unit_scope_order.h"
#include "elaborator/unpacked_array_type.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

static uint32_t InferTypeRefExprWidth(const Expr* expr,
                                      const ValueShapeOf& shape_of) {
  if (!expr) return 0;
  switch (expr->kind) {
    case ExprKind::kIdentifier:
      return shape_of(expr->text).value_or(ValueShape{}).width;
    case ExprKind::kIntegerLiteral:
      return ConstLiteralWidth(expr);
    case ExprKind::kBinary: {
      uint32_t lw = InferTypeRefExprWidth(expr->lhs, shape_of);
      uint32_t rw = InferTypeRefExprWidth(expr->rhs, shape_of);
      return std::max(lw, rw);
    }
    case ExprKind::kTernary: {
      uint32_t tw = InferTypeRefExprWidth(expr->true_expr, shape_of);
      uint32_t fw = InferTypeRefExprWidth(expr->false_expr, shape_of);
      return std::max(tw, fw);
    }
    case ExprKind::kConcatenation: {
      uint32_t total = 0;
      for (const auto* el : expr->elements) {
        total += InferTypeRefExprWidth(el, shape_of);
      }
      return total;
    }
    case ExprKind::kUnary:
      return InferTypeRefExprWidth(expr->lhs, shape_of);
    default:
      return 0;
  }
}

static bool InferTypeRefExprSigned(const Expr* expr,
                                   const ValueShapeOf& shape_of) {
  if (!expr) return false;
  switch (expr->kind) {
    case ExprKind::kIdentifier:
      return shape_of(expr->text).value_or(ValueShape{}).is_signed;
    case ExprKind::kIntegerLiteral:
      return IsSignedLiteral(expr->text);
    case ExprKind::kBinary:
      return InferTypeRefExprSigned(expr->lhs, shape_of) &&
             InferTypeRefExprSigned(expr->rhs, shape_of);
    case ExprKind::kTernary:
      return InferTypeRefExprSigned(expr->true_expr, shape_of) &&
             InferTypeRefExprSigned(expr->false_expr, shape_of);
    case ExprKind::kConcatenation:
      return false;
    case ExprKind::kUnary:
      return InferTypeRefExprSigned(expr->lhs, shape_of);
    default:
      return false;
  }
}

void SetTypeRefPackedDims(DataType& dt, uint32_t width, Arena& arena) {
  if (width <= 1) return;
  auto* left = arena.Create<Expr>();
  left->kind = ExprKind::kIntegerLiteral;
  left->int_val = static_cast<int64_t>(width - 1);
  auto* right = arena.Create<Expr>();
  right->kind = ExprKind::kIntegerLiteral;
  right->int_val = 0;
  dt.packed_dim_left = left;
  dt.packed_dim_right = right;
}

void AdoptLogicVector(DataType& dt, ValueShape shape, Arena& arena) {
  dt.kind = DataTypeKind::kLogic;
  dt.is_signed = shape.is_signed;
  SetTypeRefPackedDims(dt, shape.width, arena);
  dt.type_ref_expr = nullptr;
}

const ModuleItem* ItemNamed(std::span<ModuleItem* const> items,
                            std::string_view name) {
  auto it = std::ranges::find(items, name, &ModuleItem::name);
  return it == items.end() ? nullptr : *it;
}

const PackageDecl* PackageDeclaring(
    const CompilationUnit* unit, std::string_view name,
    const std::function<bool(std::string_view)>& reaches) {
  for (const PackageDecl* pkg : unit->packages) {
    if (reaches(pkg->name) && ItemNamed(pkg->items, name) != nullptr) {
      return pkg;
    }
  }
  return nullptr;
}

static bool ImportsFrom(const RtlirModule& mod, std::string_view package,
                        std::string_view name) {
  return std::ranges::any_of(mod.imports, [&](const RtlirImport& imp) {
    return imp.package_name == package &&
           (imp.is_wildcard || imp.item_name == name);
  });
}

DataType DeclaredValueType(const ModuleItem& item, const ValueShapeOf& shape_of,
                           Arena& arena) {
  DataType type = item.data_type;
  if (item.kind != ModuleItemKind::kParamDecl ||
      type.kind != DataTypeKind::kImplicit || type.packed_dim_left != nullptr) {
    return type;
  }
  AdoptLogicVector(type,
                   {InferTypeRefExprWidth(item.init_expr, shape_of),
                    InferTypeRefExprSigned(item.init_expr, shape_of)},
                   arena);
  return type;
}

DataType ScopeValueType(const ModuleItem& item,
                        std::span<ModuleItem* const> items, Arena& arena) {
  auto at = std::ranges::find(items, &item);
  std::span<ModuleItem* const> ahead =
      items.first(static_cast<size_t>(at - items.begin()));
  return DeclaredValueType(
      item,
      [&](std::string_view name) {
        return ScopeValueShape(name, ahead, arena);
      },
      arena);
}

using EnumDeclaringVisitor = std::function<void(
    const ModuleItem& item, std::string_view path, const DataType& type)>;

static void ForEachEnumDeclaring(std::string_view name,
                                 std::span<ModuleItem* const> items,
                                 const EnumDeclaringVisitor& fn) {
  for (const ModuleItem* item : items) {
    ForEachEnumTypeOfItem(
        item, [&](std::string_view path, const DataType& type) {
          for (const EnumMember& member : type.enum_members) {
            const std::vector<std::string> kNames =
                EnumMemberDeclaredNames(member, {});
            if (std::ranges::find(kNames, name) != kNames.end())
              fn(*item, path, type);
          }
        });
  }
}

std::optional<ValueShape> EnumConstantShape(
    std::string_view name, std::span<ModuleItem* const> items) {
  std::optional<ValueShape> shape;
  ForEachEnumDeclaring(
      name, items,
      [&](const ModuleItem&, std::string_view, const DataType& type) {
        shape = ValueShape{EvalTypeWidth(type), IsSignedType(type, {})};
      });
  return shape;
}

std::optional<ValueShape> ScopeValueShape(std::string_view name,
                                          std::span<ModuleItem* const> items,
                                          Arena& arena) {
  auto param = std::ranges::find_if(items, [&](const ModuleItem* i) {
    return i->kind == ModuleItemKind::kParamDecl && i->name == name;
  });
  if (param == items.end()) return EnumConstantShape(name, items);
  DataType type = ScopeValueType(**param, items, arena);
  return ValueShape{EvalTypeWidth(type), type.is_signed};
}

static DataType NamedBehind(std::string_view scope,
                            std::string_view type_name) {
  DataType named;
  named.kind = DataTypeKind::kNamed;
  named.scope_name = scope;
  named.type_name = type_name;
  return named;
}

static std::optional<DataType> ScopeEnumConstantType(
    std::string_view name, std::string_view scope,
    std::span<ModuleItem* const> items) {
  std::optional<DataType> type;
  ForEachEnumDeclaring(
      name, items,
      [&](const ModuleItem& item, std::string_view path,
          const DataType& enumeration) {
        type = enumeration;
        if (item.kind == ModuleItemKind::kTypedef && path.empty())
          type = NamedBehind(scope, item.name);
      });
  return type;
}

std::optional<DataType> OuterValueType(std::string_view name,
                                       const TypeRefScope& scope) {
  for (const PackageDecl* pkg : scope.unit->packages) {
    if (!ImportsFrom(*scope.mod, pkg->name, name)) continue;
    if (const ModuleItem* item = ItemNamed(pkg->items, name))
      return ScopeValueType(*item, pkg->items, scope.arena);
    if (std::optional<DataType> constant =
            ScopeEnumConstantType(name, pkg->name, pkg->items))
      return constant;
  }
  const std::vector<ModuleItem*> kItems =
      UnitItemsBefore(scope.unit, scope.reference);
  const ModuleItem* item = ItemNamed(kItems, name);
  if (item == nullptr) return std::nullopt;
  return ScopeValueType(*item, kItems, scope.arena);
}

const PackageDecl* PackageNamed(const CompilationUnit& unit,
                                std::string_view name) {
  auto it = std::ranges::find_if(unit.packages, [&](const PackageDecl* p) {
    return p != nullptr && p->name == name;
  });
  return it != unit.packages.end() ? *it : nullptr;
}

static DataType BehindScope(DataType type, std::span<ModuleItem* const> items,
                            std::string_view scope) {
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty())
    return type;
  const ModuleItem* item = ItemNamed(items, type.type_name);
  if (item != nullptr && item->kind == ModuleItemKind::kTypedef)
    type.scope_name = scope;
  return type;
}

static bool DeclaresValue(const ModuleItem& item) {
  return item.kind == ModuleItemKind::kVarDecl ||
         item.kind == ModuleItemKind::kNetDecl ||
         (item.kind == ModuleItemKind::kParamDecl &&
          item.data_type.kind != DataTypeKind::kVoid);
}

std::optional<DeclaredValue> ScopeValue(std::span<ModuleItem* const> items,
                                        std::string_view scope,
                                        std::string_view name,
                                        const OuterScope& outer) {
  const ModuleItem* item = ItemNamed(items, name);
  if (item == nullptr) {
    std::optional<DataType> constant =
        ScopeEnumConstantType(name, scope, items);
    if (!constant) return std::nullopt;
    return DeclaredValue{std::move(*constant)};
  }
  if (!DeclaresValue(*item)) return std::nullopt;
  DeclaredValue value{
      BehindScope(ScopeValueType(*item, items, outer.arena), items, scope),
      static_cast<uint32_t>(item->unpacked_dims.size())};
  value.dims = item->unpacked_dims;
  if (!value.dims.empty())
    value.outermost = UnpackedDimKind(value.dims.front(), outer.tables);
  return value;
}

static std::vector<ModuleItem*> UnitItemsSearched(const OuterScope& outer) {
  if (outer.reference == nullptr) return {};
  return UnitItemsBefore(outer.unit, outer.reference->range.start);
}

std::optional<DeclaredValue> ScopedValue(std::string_view prefix,
                                         std::string_view name,
                                         const OuterScope& outer) {
  if (outer.unit == nullptr) return std::nullopt;
  if (prefix == "$unit")
    return ScopeValue(UnitItemsSearched(outer), prefix, name, outer);
  const PackageDecl* pkg = PackageNamed(*outer.unit, prefix);
  if (pkg == nullptr) return std::nullopt;
  return ScopeValue(pkg->items, pkg->name, name, outer);
}

std::optional<DeclaredValue> ImportedValue(std::span<ModuleItem* const> items,
                                           std::string_view name,
                                           const OuterScope& outer) {
  for (const ModuleItem* item : items) {
    if (item == nullptr || item->kind != ModuleItemKind::kImportDecl) continue;
    const ImportItem& import = item->import_item;
    if (!import.is_wildcard && import.item_name != name) continue;
    const PackageDecl* pkg = PackageNamed(*outer.unit, import.package_name);
    if (pkg == nullptr) continue;
    if (std::optional<DeclaredValue> value =
            ScopeValue(pkg->items, pkg->name, name, outer)) {
      return value;
    }
  }
  return std::nullopt;
}

std::optional<DeclaredValue> OuterValue(const RtlirModule& mod,
                                        std::string_view name,
                                        const OuterScope& outer) {
  if (outer.unit == nullptr) return std::nullopt;
  for (const PackageDecl* pkg : outer.unit->packages) {
    if (!ImportsFrom(mod, pkg->name, name)) continue;
    if (std::optional<DeclaredValue> value =
            ScopeValue(pkg->items, pkg->name, name, outer)) {
      return value;
    }
  }
  return ScopeValue(UnitItemsSearched(outer), "$unit", name, outer);
}

}  // namespace delta
