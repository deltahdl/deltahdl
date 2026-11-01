#include "elaborator/scope_value_type.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "elaborator/unit_scope_order.h"
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
    // §5.7.1: a simple decimal number is signed, and a based one only where
    // its base carries the s designator.
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

// §6.23: build the packed dimension [width-1:0] of a type_reference resolved to
// a known scalar/vector width (no dimension is added for a 1-bit scalar).
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

// Takes onto `dt`, in place of its type reference, the logic vector of
// `shape`'s width and signing.
void AdoptLogicVector(DataType& dt, ValueShape shape, Arena& arena) {
  dt.kind = DataTypeKind::kLogic;
  dt.is_signed = shape.is_signed;
  SetTypeRefPackedDims(dt, shape.width, arena);
  dt.type_ref_expr = nullptr;
}

// The item of `items` written `name`, or null where none is.
const ModuleItem* ItemNamed(std::span<ModuleItem* const> items,
                            std::string_view name) {
  auto it = std::ranges::find(items, name, &ModuleItem::name);
  return it == items.end() ? nullptr : *it;
}

// The first package of `unit` that `reaches` answers true for and that
// declares an item written `name`, or null where none does.
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

// §26.3: whether `mod` imports `name` from `package`, by name or by a
// wildcard.
static bool ImportsFrom(const RtlirModule& mod, std::string_view package,
                        std::string_view name) {
  return std::ranges::any_of(mod.imports, [&](const RtlirImport& imp) {
    return imp.package_name == package &&
           (imp.is_wildcard || imp.item_name == name);
  });
}

// The type of the value `item` declares, which a type reference to it stands
// for: the type the declaration writes, or, for a parameter written with
// neither a type nor a range, the self-determined type of its value
// (§6.20.2), whose names `shape_of` reads in the scope the declaration is
// written in.
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

// §6.20.2 with §26.2 and §3.12.1: the type of the value `item` declares among
// `items`, the declarations of a package or of the compilation unit. A
// parameter of no type takes its value's, whose names are those `items`
// declares ahead of the parameter (ScopeValueShape).
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

// §6.19 with §6.19.3: the shape of the enumeration constant `name` that one
// of `items` declares, which is of the enumeration's type. A `name[N]`
// member declares the constants it generates (EnumMemberDeclaredNames).
// Empty where `items` declares no constant of the name.
std::optional<ValueShape> EnumConstantShape(
    std::string_view name, std::span<ModuleItem* const> items) {
  std::optional<ValueShape> shape;
  const auto kVisit = [&](std::string_view, const DataType& type) {
    for (const EnumMember& member : type.enum_members) {
      const std::vector<std::string> kNames =
          EnumMemberDeclaredNames(member, {});
      if (std::ranges::find(kNames, name) == kNames.end()) continue;
      shape = ValueShape{EvalTypeWidth(type), IsSignedType(type, {})};
    }
  };
  for (const ModuleItem* item : items) ForEachEnumTypeOfItem(item, kVisit);
  return shape;
}

// The shape of the parameter or enumeration constant `name` among `items`,
// the declarations of a package or of the compilation unit ahead of the
// parameter whose value reads it: a parameter's from the type its own
// declaration writes or its own value's (ScopeValueType), a constant's from
// its enumeration (EnumConstantShape). A parameter's value being a constant
// expression, the values it names are these rather than variables or nets.
// Empty where `items` declares neither of the name.
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

// §26.3 with §3.12.1: the type of the value `name` names outside the module,
// read in the scope declaring it (ScopeValueType): one a package the module
// imports it from declares, or else one of the compilation unit written before
// the reference. Nothing where neither is.
std::optional<DataType> OuterValueType(std::string_view name,
                                       const TypeRefScope& scope) {
  const PackageDecl* pkg =
      PackageDeclaring(scope.unit, name, [&](std::string_view package) {
        return ImportsFrom(*scope.mod, package, name);
      });
  const std::vector<ModuleItem*> kItems =
      pkg != nullptr ? pkg->items
                     : UnitItemsBefore(scope.unit, scope.reference);
  const ModuleItem* item = ItemNamed(kItems, name);
  if (item == nullptr) return std::nullopt;
  return ScopeValueType(*item, kItems, scope.arena);
}

}  // namespace delta
