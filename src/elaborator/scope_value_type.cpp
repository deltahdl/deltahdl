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

// What ForEachEnumDeclaring hands each enumeration it finds: the item
// declaring it, the path ForEachEnumTypeOfItem gives it within the item's type,
// and the enumeration.
using EnumDeclaringVisitor = std::function<void(
    const ModuleItem& item, std::string_view path, const DataType& type)>;

// Calls `fn` for each enumeration one of `items` declares with a named
// constant `name`. A `name[N]` member declares the constants it generates
// (EnumMemberDeclaredNames).
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

// §6.19 with §6.19.3: the shape of the enumeration constant `name` that one
// of `items` declares, which is of the enumeration's type. A `name[N]`
// member declares the constants it generates (EnumMemberDeclaredNames).
// Empty where `items` declares no constant of the name.
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

// The typedef name `type_name` read behind the scope `scope`.
static DataType NamedBehind(std::string_view scope,
                            std::string_view type_name) {
  DataType named;
  named.kind = DataTypeKind::kNamed;
  named.scope_name = scope;
  named.type_name = type_name;
  return named;
}

// §6.19.3: the type of the enumeration constant `name` one of `items`
// declares: the typedef naming the enumeration, read behind `scope`, or the
// enumeration as written where no typedef names it.
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

// §26.3 with §3.12.1: the type of the value `name` names outside the module,
// read in the scope declaring it (ScopeValueType): one a package the module
// imports it from declares, an enumeration constant among them, whose type
// is its enumeration's (ScopeEnumConstantType), or else one of the
// compilation unit written before the reference. Nothing where neither is.
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

// The package `unit` declares as `name`; null where it declares none.
const PackageDecl* PackageNamed(const CompilationUnit& unit,
                                std::string_view name) {
  auto it = std::ranges::find_if(unit.packages, [&](const PackageDecl* p) {
    return p != nullptr && p->name == name;
  });
  return it != unit.packages.end() ? *it : nullptr;
}

// `type` read behind `scope` where it is written bare by the name of a typedef
// `items` declare, as the table of typedefs records it; `type` as it is
// otherwise.
static DataType BehindScope(DataType type, std::span<ModuleItem* const> items,
                            std::string_view scope) {
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty())
    return type;
  const ModuleItem* item = ItemNamed(items, type.type_name);
  if (item != nullptr && item->kind == ModuleItemKind::kTypedef)
    type.scope_name = scope;
  return type;
}

// Whether `item` declares a value: a variable, a net or a value parameter,
// whose type is not the void a type parameter's records (§6.20.3).
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

// §3.12.1: the items of the compilation unit a reference in the module of
// `outer` searches, those written before the module; none where no module is
// known.
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

// §26.3 with §3.12.1: a package's import comes first, then the compilation
// unit, as OuterValueType reads them.
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
