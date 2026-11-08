#include "elaborator/param_value_assignability.h"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/net_data_type.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

std::optional<ParamValueShape> NoNamedShape(std::string_view) {
  return std::nullopt;
}

namespace {

using Kind = ParamValueKind;

constexpr std::array<std::string_view, 14> kNumericCastTypes = {
    "bit",     "logic", "reg",  "byte",      "shortint", "int",    "longint",
    "integer", "time",  "real", "shortreal", "realtime", "signed", "unsigned"};

ParamValueShape OfKind(Kind kind) {
  ParamValueShape shape;
  shape.kind = kind;
  return shape;
}

uint64_t TypeIdentity(const DataType& type) {
  return (uint64_t{type.decl_loc.file_id} << 48) |
         (uint64_t{type.decl_loc.line} << 20) | type.decl_loc.column;
}

ParamValueShape OfIdentity(Kind kind, const DataType& type) {
  ParamValueShape shape = OfKind(kind);
  shape.identity = TypeIdentity(type);
  return shape;
}

bool IsNumeric(Kind kind) {
  return kind == Kind::kNumber || kind == Kind::kEnum ||
         kind == Kind::kStringLiteral;
}

std::vector<uint64_t> DimSizes(const std::vector<Expr*>& dims,
                               const ScopeMap& constants) {
  std::vector<uint64_t> sizes;
  sizes.reserve(dims.size());
  for (const Expr* dim : dims) {
    auto folded = FoldUnpackedDimBounds(dim, constants);
    sizes.push_back(folded ? folded->Size() : 0);
  }
  return sizes;
}

ParamValueShape ArrayShape(std::vector<uint64_t> dims,
                           const DataType& element) {
  ParamValueShape shape = OfKind(Kind::kArray);
  shape.dims = std::move(dims);
  shape.element = element;
  return shape;
}

ParamValueShape ResolvedShape(const DataType& resolved) {
  switch (resolved.kind) {
    case DataTypeKind::kEnum:
      return OfIdentity(Kind::kEnum, resolved);
    case DataTypeKind::kString:
      return OfKind(Kind::kString);
    case DataTypeKind::kStruct:
    case DataTypeKind::kUnion:
      return IsUnpackedAggregateType(resolved)
                 ? OfIdentity(Kind::kStructure, resolved)
                 : OfKind(Kind::kNumber);
    default:
      return OfKind(Kind::kNumber);
  }
}

std::optional<ParamValueShape> TypedefArrayShape(
    const std::vector<std::string_view>& names, const ParamValueScope& scope) {
  for (std::string_view name : names) {
    auto dims = scope.tables.typedef_dims.find(name);
    if (dims == scope.tables.typedef_dims.end()) continue;
    return ArrayShape(DimSizes(dims->second, scope.constants),
                      scope.tables.typedefs.at(name));
  }
  return std::nullopt;
}

ParamValueShape DeclaredShape(const DataType& type, std::vector<uint64_t> dims,
                              const ParamValueScope& scope) {
  if (!dims.empty()) return ArrayShape(std::move(dims), type);
  const std::string kKey = NamedTypeKey(type);
  DataType keyed = type;
  keyed.type_name = kKey;
  std::vector<std::string_view> names;
  const DataType* resolved =
      FollowTypedefs(keyed, scope.tables.typedefs, names);
  if (auto array = TypedefArrayShape(names, scope)) return *std::move(array);
  if (resolved != nullptr) return ResolvedShape(*resolved);
  if (scope.tables.class_names.count(names.back()) == 0) return {};
  ParamValueShape shape = OfKind(Kind::kClass);
  shape.class_name = names.back();
  return shape;
}

ParamValueShape TargetShape(const DataType& type,
                            const std::vector<Expr*>& dims,
                            const ParamValueScope& scope) {
  if (type.kind == DataTypeKind::kImplicit) return {};
  return DeclaredShape(type, DimSizes(dims, scope.constants), scope);
}

ParamValueShape ParamDeclTargetShape(const RtlirParamDecl& pd,
                                     const ParamValueScope& scope) {
  static const std::vector<Expr*> kNoDims;
  const DataType* type =
      pd.type_param_actual != nullptr ? pd.type_param_actual : pd.decl_type;
  if (type == nullptr) return {};
  return TargetShape(
      *type, pd.unpacked_dims != nullptr ? *pd.unpacked_dims : kNoDims, scope);
}

ParamValueShape ValueShapeOf(const Expr* value, const ParamValueScope& scope);

std::optional<ParamValueShape> ScopedParamShape(std::string_view owner,
                                                std::string_view name,
                                                const ParamValueScope& scope);

ParamValueShape ValueOrTargetShape(const ParamValueShape& target,
                                   const Expr* value,
                                   const ParamValueScope& scope) {
  if (target.kind != Kind::kUnknown || value == nullptr) return target;
  return ValueShapeOf(value, scope);
}

ParamValueShape EnumConstantShape(std::string_view name,
                                  const TypedefMap& typedefs) {
  std::vector<uint64_t> owners;
  for (const auto& entry : typedefs) {
    const DataType& type = entry.second;
    if (std::ranges::find(type.enum_members, name, &EnumMember::name) !=
        type.enum_members.end())
      owners.push_back(TypeIdentity(type));
  }
  if (owners.empty()) return {};
  std::ranges::sort(owners);
  const auto kRepeated = std::ranges::unique(owners);
  owners.erase(kRepeated.begin(), kRepeated.end());
  ParamValueShape shape = OfKind(Kind::kEnum);
  shape.identity = owners.size() == 1 ? owners.front() : 0;
  return shape;
}

ParamValueShape NamedShape(const Expr* value, const ParamValueScope& scope) {
  if (value->text == "null") return OfKind(Kind::kNull);
  std::optional<ParamValueShape> shape =
      value->scope_prefix.empty()
          ? scope.named(value->text)
          : ScopedParamShape(value->scope_prefix, value->text, scope);
  if (shape) return *std::move(shape);
  return EnumConstantShape(value->text, scope.tables.typedefs);
}

ParamValueShape QualifiedShape(const Expr* value,
                               const ParamValueScope& scope) {
  if (auto shape = ScopedParamShape(value->lhs->text, value->rhs->text, scope))
    return *std::move(shape);
  return EnumConstantShape(value->rhs->text, scope.tables.typedefs);
}

DataType NamedType(std::string_view scope_name, std::string_view type_name) {
  DataType named;
  named.kind = DataTypeKind::kNamed;
  named.scope_name = scope_name;
  named.type_name = type_name;
  return named;
}

ParamValueShape CastTypeShape(const Expr* type_node,
                              const ParamValueScope& scope) {
  if (type_node->kind != ExprKind::kMemberAccess) return OfKind(Kind::kNumber);
  return DeclaredShape(NamedType(type_node->lhs->text, type_node->rhs->text),
                       {}, scope);
}

ParamValueShape CastShape(const Expr* cast, const ParamValueScope& scope) {
  const std::string_view kType = cast->text;
  if (kType.empty()) return CastTypeShape(cast->rhs, scope);
  if (kType == "const") return ValueShapeOf(cast->lhs, scope);
  if (kType == "string") return OfKind(Kind::kString);
  if (std::ranges::find(kNumericCastTypes, kType) != kNumericCastTypes.end())
    return OfKind(Kind::kNumber);
  return DeclaredShape(NamedType({}, kType), {}, scope);
}

ParamValueShape TernaryShape(const Expr* ternary,
                             const ParamValueScope& scope) {
  ParamValueShape when_true = ValueShapeOf(ternary->true_expr, scope);
  const ParamValueShape kWhenFalse = ValueShapeOf(ternary->false_expr, scope);
  if (when_true.kind == kWhenFalse.kind &&
      when_true.identity == kWhenFalse.identity)
    return when_true;
  return OfKind(IsNumeric(when_true.kind) && IsNumeric(kWhenFalse.kind)
                    ? Kind::kNumber
                    : Kind::kUnknown);
}

ParamValueShape ConcatShape(const Expr* concat, const ParamValueScope& scope) {
  bool text = true;
  bool any_string = false;
  for (const Expr* item : concat->elements) {
    const Kind kKind = ValueShapeOf(item, scope).kind;
    text = text && (kKind == Kind::kString || kKind == Kind::kStringLiteral);
    any_string = any_string || kKind == Kind::kString;
  }
  if (!text) return OfKind(Kind::kNumber);
  return OfKind(any_string ? Kind::kString : Kind::kStringLiteral);
}

ParamValueShape ValueShapeOf(const Expr* value, const ParamValueScope& scope) {
  switch (value->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
    case ExprKind::kUnary:
    case ExprKind::kBinary:
      return OfKind(Kind::kNumber);
    case ExprKind::kStringLiteral:
      return OfKind(Kind::kStringLiteral);
    case ExprKind::kIdentifier:
      return NamedShape(value, scope);
    case ExprKind::kMemberAccess:
      return value->is_scope_resolution ? QualifiedShape(value, scope)
                                        : ParamValueShape{};
    case ExprKind::kAssignmentPattern:
      return OfKind(Kind::kPattern);
    case ExprKind::kCast:
      return CastShape(value, scope);
    case ExprKind::kTernary:
      return TernaryShape(value, scope);
    case ExprKind::kConcatenation:
    case ExprKind::kReplicate:
      return ConcatShape(value, scope);
    default:
      return {};
  }
}

bool SameIdentity(const ParamValueShape& target, const ParamValueShape& value) {
  return value.identity == 0 || value.identity == target.identity;
}

const DataType* Resolved(const DataType* type, const TypedefMap& typedefs) {
  std::vector<std::string_view> names;
  const DataType* resolved = FollowTypedefs(*type, typedefs, names);
  return resolved != nullptr ? resolved : type;
}

bool DimsMatch(uint64_t target, uint64_t value) {
  return target == 0 || value == 0 || target == value;
}

bool ArraysAssignable(const ParamValueShape& target,
                      const ParamValueShape& value,
                      const TypedefMap& typedefs) {
  return std::ranges::equal(target.dims, value.dims, DimsMatch) &&
         TypesEquivalent(*Resolved(&target.element, typedefs),
                         *Resolved(&value.element, typedefs));
}

bool ShapeAssignable(const ParamValueShape& target,
                     const ParamValueShape& value,
                     const ParamValueScope& scope) {
  if (target.kind == Kind::kUnknown || value.kind == Kind::kUnknown)
    return true;
  switch (target.kind) {
    case Kind::kNumber:
      return IsNumeric(value.kind) || value.kind == Kind::kPattern;
    case Kind::kString:
      return value.kind == Kind::kString || value.kind == Kind::kStringLiteral;
    case Kind::kEnum:
      return value.kind == Kind::kEnum && SameIdentity(target, value);
    case Kind::kArray:
      return value.kind == Kind::kPattern ||
             (value.kind == Kind::kArray &&
              ArraysAssignable(target, value, scope.tables.typedefs));
    case Kind::kStructure:
      return value.kind == Kind::kPattern ||
             (value.kind == Kind::kStructure && SameIdentity(target, value));
    default:
      return value.kind == Kind::kNull ||
             (value.kind == Kind::kClass &&
              IsClassDerivedFrom(value.class_name, target.class_name,
                                 scope.unit));
  }
}

struct ParamValueTarget {
  std::string_view name;
  const ParamValueShape& shape;
};

bool ValueAssignable(const ParamValueShape& target, const Expr* value,
                     const ParamValueScope& scope) {
  return value == nullptr ||
         ShapeAssignable(target, ValueShapeOf(value, scope), scope);
}

void ReportNotAssignable(std::string_view name, SourceLoc loc,
                         DiagEngine& diag) {
  diag.ErrorOnce(loc,
                 std::format("the value given to parameter '{}' is not "
                             "assignment compatible with its type",
                             name),
                 Subclause("6.20.2"));
}

void ReportIfNotAssignable(const ParamValueTarget& target, const Expr* value,
                           const ParamValueScope& scope, DiagEngine& diag) {
  if (ValueAssignable(target.shape, value, scope)) return;
  ReportNotAssignable(target.name, value->range.start, diag);
}

DataType ScopedType(const DataType& type, const PackageDecl* package) {
  return package != nullptr ? InPackageScope(type, *package) : type;
}

ParamValueScope Crossed(const ParamValueScope& scope) {
  return {scope.tables, scope.constants, scope.unit, NoNamedShape, false};
}

struct ItemScope {
  std::span<ModuleItem* const> items;
  const PackageDecl* package;
};

ParamValueShape ItemTargetShape(const ModuleItem& item,
                                const PackageDecl* package,
                                const ParamValueScope& scope) {
  return TargetShape(ScopedType(item.data_type, package), item.unpacked_dims,
                     scope);
}

ParamShapeLookup ItemParamShapes(const ItemScope& where,
                                 const ParamValueScope& scope);

std::optional<ParamValueShape> OwnParamShape(const ItemScope& where,
                                             std::string_view name,
                                             const ParamValueScope& scope) {
  for (std::size_t i = 0; i < where.items.size(); ++i) {
    const ModuleItem& item = *where.items[i];
    if (item.kind != ModuleItemKind::kParamDecl || item.name != name) continue;
    const ParamValueScope kDeclared{
        scope.tables, scope.constants, scope.unit,
        ItemParamShapes({where.items.first(i), where.package}, scope),
        scope.crosses_scopes};
    return ValueOrTargetShape(ItemTargetShape(item, where.package, scope),
                              item.init_expr, kDeclared);
  }
  return std::nullopt;
}

const PackageDecl* PackageNamed(std::string_view name,
                                const CompilationUnit* unit) {
  for (const PackageDecl* pkg : unit->packages) {
    if (pkg->name == name) return pkg;
  }
  return nullptr;
}

std::optional<ParamValueShape> PackageParamShape(std::string_view package,
                                                 std::string_view name,
                                                 const ParamValueScope& scope) {
  const PackageDecl* pkg = PackageNamed(package, scope.unit);
  if (pkg == nullptr) return std::nullopt;
  return OwnParamShape({pkg->items, pkg}, name, scope);
}

bool ImportsName(const ModuleItem& item, std::string_view name) {
  return item.kind == ModuleItemKind::kImportDecl &&
         (item.import_item.is_wildcard || item.import_item.item_name == name);
}

std::optional<ParamValueShape> ImportedParamShape(
    std::span<ModuleItem* const> items, std::string_view name,
    const ParamValueScope& scope) {
  for (const ModuleItem* item : items) {
    if (!ImportsName(*item, name)) continue;
    if (auto shape = PackageParamShape(item->import_item.package_name, name,
                                       Crossed(scope)))
      return shape;
  }
  return std::nullopt;
}

std::optional<ParamValueShape> UnitParamShape(std::string_view name,
                                              const ParamValueScope& scope) {
  if (auto shape =
          OwnParamShape({scope.unit->cu_items, nullptr}, name, Crossed(scope)))
    return shape;
  return ImportedParamShape(scope.unit->cu_items, name, scope);
}

ParamShapeLookup ItemParamShapes(const ItemScope& where,
                                 const ParamValueScope& scope) {
  return
      [where, &scope](std::string_view name) -> std::optional<ParamValueShape> {
        if (auto shape = OwnParamShape(where, name, scope)) return shape;
        if (!scope.crosses_scopes) return std::nullopt;
        if (auto shape = ImportedParamShape(where.items, name, scope))
          return shape;
        if (where.package != nullptr) return std::nullopt;
        return UnitParamShape(name, scope);
      };
}

struct ModuleLookup {
  ParamModuleSite site;
  std::vector<std::string_view>& untyped_names;
  std::size_t count;
};

std::optional<std::size_t> VisibleParam(const ModuleLookup& where,
                                        std::string_view name) {
  const std::vector<RtlirParamDecl>& params = where.site.module.params;
  std::optional<std::size_t> found;
  for (std::size_t i = 0; i < where.count; ++i) {
    if (params[i].name == name &&
        where.site.prefix.starts_with(params[i].gen_block_prefix))
      found = i;
  }
  return found;
}

const std::vector<ModuleItem*>& ModuleItemsOf(const RtlirModule& module) {
  static const std::vector<ModuleItem*> kNoItems;
  return module.decl != nullptr ? module.decl->items : kNoItems;
}

ParamShapeLookup ModuleScopeShapes(const ModuleLookup& where,
                                   const ParamValueScope& scope);

ParamValueShape ModuleParamShape(const ModuleLookup& where, std::size_t index,
                                 const ParamValueScope& scope) {
  const RtlirParamDecl& pd = where.site.module.params[index];
  ParamValueShape target = ParamDeclTargetShape(pd, scope);
  if (target.kind != Kind::kUnknown || pd.from_override) return target;
  where.untyped_names.push_back(pd.name);
  const ParamValueScope kDeclared{
      scope.tables, scope.constants, scope.unit,
      ModuleScopeShapes({{where.site.module, pd.gen_block_prefix},
                         where.untyped_names,
                         index},
                        scope)};
  return ValueOrTargetShape(target, pd.default_value, kDeclared);
}

ParamShapeLookup ModuleScopeShapes(const ModuleLookup& where,
                                   const ParamValueScope& scope) {
  return [where,
          &scope](std::string_view name) -> std::optional<ParamValueShape> {
    if (std::optional<std::size_t> found = VisibleParam(where, name))
      return ModuleParamShape(where, *found, scope);
    if (auto shape =
            ImportedParamShape(ModuleItemsOf(where.site.module), name, scope))
      return shape;
    return UnitParamShape(name, scope);
  };
}

bool OverriddenByName(const std::vector<RtlirParamDecl>& params,
                      std::string_view name) {
  return std::ranges::any_of(params, [name](const RtlirParamDecl& pd) {
    return pd.name == name && pd.from_override;
  });
}

struct ScopedClass {
  const ClassDecl& cls;
  const PackageDecl* package;
};

const PackageDecl* PackageDeclaring(const ClassDecl& cls,
                                    const CompilationUnit* unit) {
  for (const PackageDecl* pkg : unit->packages) {
    if (std::ranges::any_of(pkg->items, [&cls](const ModuleItem* item) {
          return item->class_decl == &cls;
        }))
      return pkg;
  }
  return nullptr;
}

ScopedClass InDeclaringScope(const ClassDecl& cls,
                             const CompilationUnit* unit) {
  return {cls, PackageDeclaring(cls, unit)};
}

ParamValueShape ClassPortTargetShape(const ScopedClass& where,
                                     std::size_t index,
                                     const ParamValueScope& scope) {
  static const std::vector<Expr*> kNoDims;
  const ClassDecl& cls = where.cls;
  auto dims = cls.param_port_unpacked_dims.find(cls.params[index].first);
  return TargetShape(
      ScopedType(cls.param_types[index], where.package),
      dims != cls.param_port_unpacked_dims.end() ? dims->second : kNoDims,
      scope);
}

bool IsParamMember(const ClassMember& member) {
  return member.kind == ClassMemberKind::kProperty && member.is_param;
}

ParamValueShape MemberTargetShape(const ClassMember& member,
                                  const PackageDecl* package,
                                  const ParamValueScope& scope) {
  return TargetShape(ScopedType(member.data_type, package),
                     member.unpacked_dims, scope);
}

struct ClassLimit {
  std::size_t ports;
  std::size_t members;
};

ClassLimit WholeClass(const ClassDecl& cls) {
  return {cls.params.size(), cls.members.size()};
}

ParamShapeLookup ClassParamShapes(const ScopedClass& where,
                                  const ParamValueScope& outer,
                                  const ClassLimit& limit);

std::optional<ParamValueShape> ClassParamShape(const ScopedClass& where,
                                               const ClassLimit& limit,
                                               std::string_view name,
                                               const ParamValueScope& outer) {
  const ClassDecl& cls = where.cls;
  for (std::size_t i = 0; i < limit.ports; ++i) {
    if (cls.params[i].first != name) continue;
    const ParamValueScope kDeclared{outer.tables, outer.constants, outer.unit,
                                    ClassParamShapes(where, outer, {i, 0}),
                                    outer.crosses_scopes};
    return ValueOrTargetShape(ClassPortTargetShape(where, i, outer),
                              cls.params[i].second, kDeclared);
  }
  for (std::size_t i = 0; i < limit.members; ++i) {
    const ClassMember& member = *cls.members[i];
    if (!IsParamMember(member) || member.name != name) continue;
    const ParamValueScope kDeclared{
        outer.tables, outer.constants, outer.unit,
        ClassParamShapes(where, outer, {cls.params.size(), i}),
        outer.crosses_scopes};
    return ValueOrTargetShape(MemberTargetShape(member, where.package, outer),
                              member.init_expr, kDeclared);
  }
  return outer.named(name);
}

ParamShapeLookup ClassParamShapes(const ScopedClass& where,
                                  const ParamValueScope& outer,
                                  const ClassLimit& limit) {
  return [where, &outer, limit](std::string_view name) {
    return ClassParamShape(where, limit, name, outer);
  };
}

std::optional<ParamValueShape> ScopedParamShape(std::string_view owner,
                                                std::string_view name,
                                                const ParamValueScope& scope) {
  if (!scope.crosses_scopes) return std::nullopt;
  const ParamValueScope kCrossed = Crossed(scope);
  if (owner == "$unit")
    return OwnParamShape({scope.unit->cu_items, nullptr}, name, kCrossed);
  if (auto shape = PackageParamShape(owner, name, kCrossed)) return shape;
  const ClassDecl* cls = FindClassDecl(owner, scope.unit);
  if (cls == nullptr) return std::nullopt;
  return ClassParamShapes(InDeclaringScope(*cls, scope.unit), kCrossed,
                          WholeClass(*cls))(name);
}

void ReportSpecializationArgs(const ScopedClass& where,
                              const std::vector<DataType>& args,
                              const ParamValueScope& scope, DiagEngine& diag) {
  const ClassDecl& cls = where.cls;
  for (std::size_t i = 0; i < cls.params.size(); ++i) {
    const DataType* arg = SpecializationArgument(args, i, cls.params[i].first);
    if (arg == nullptr) continue;
    ReportIfNotAssignable(
        {cls.params[i].first, ClassPortTargetShape(where, i, scope)},
        arg->type_ref_expr, scope, diag);
  }
}

void ReportWrittenSpecialization(const DataType& type,
                                 const ParamValueScope& scope,
                                 DiagEngine& diag) {
  if (type.type_params.empty()) return;
  const ClassDecl* cls = FindClassDecl(type.type_name, scope.unit);
  if (cls == nullptr) return;
  ReportSpecializationArgs(InDeclaringScope(*cls, scope.unit), type.type_params,
                           scope, diag);
}

using BlockParams = std::vector<std::pair<std::string_view, ParamValueShape>>;

struct ProcedureScope {
  const ParamValueScope& outer;
  const PackageDecl* package;
};

ParamShapeLookup BlockShapes(const ProcedureScope& where,
                             const BlockParams& block) {
  return [&where,
          &block](std::string_view name) -> std::optional<ParamValueShape> {
    for (auto it = block.rbegin(); it != block.rend(); ++it) {
      if (it->first == name) return it->second;
    }
    return where.outer.named(name);
  };
}

void ReportStmtDecl(const Stmt& s, const ProcedureScope& where,
                    BlockParams& block, DiagEngine& diag) {
  const ParamValueScope kHere{where.outer.tables, where.outer.constants,
                              where.outer.unit, BlockShapes(where, block)};
  ReportWrittenSpecialization(s.var_decl_type, kHere, diag);
  if (!s.var_is_param) {
    block.emplace_back(s.var_name, ParamValueShape{});
    return;
  }
  const ModuleItem& param = *s.decl_item;
  const ParamValueShape kTarget = TargetShape(
      ScopedType(param.data_type, where.package), param.unpacked_dims, kHere);
  ReportIfNotAssignable({param.name, kTarget}, param.init_expr, kHere, diag);
  block.emplace_back(param.name,
                     ValueOrTargetShape(kTarget, param.init_expr, kHere));
}

void ReportStmtParams(const Stmt* s, const ProcedureScope& where,
                      BlockParams& block, DiagEngine& diag) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl) ReportStmtDecl(*s, where, block, diag);
  BlockParams inner = block;
  ForEachChildStmt(s, [&where, &inner, &diag](const Stmt* sub) {
    ReportStmtParams(sub, where, inner, diag);
  });
}

void ReportProcedureParams(const ModuleItem& item, const ParamValueScope& outer,
                           const PackageDecl* package, DiagEngine& diag) {
  const ProcedureScope kWhere{outer, package};
  BlockParams top{{item.name, ParamValueShape{}}};
  for (const FunctionArg& arg : item.func_args)
    top.emplace_back(arg.name, ParamValueShape{});
  for (const Stmt* s : item.func_body_stmts)
    ReportStmtParams(s, kWhere, top, diag);
  ReportStmtParams(item.body, kWhere, top, diag);
  ReportWrittenSpecialization(item.return_type, outer, diag);
  for (const FunctionArg& arg : item.func_args)
    ReportWrittenSpecialization(arg.data_type, outer, diag);
}

void ReportItemParams(const ItemScope& where, const ParamValueScope& scope,
                      DiagEngine& diag) {
  const ParamValueScope kInner{scope.tables, scope.constants, scope.unit,
                               ItemParamShapes(where, scope)};
  for (const ModuleItem* item : where.items) {
    ReportProcedureParams(*item, kInner, where.package, diag);
    ReportWrittenSpecialization(item->data_type, kInner, diag);
    ReportWrittenSpecialization(item->typedef_type, kInner, diag);
    if (item->kind != ModuleItemKind::kParamDecl) continue;
    ReportIfNotAssignable(
        {item->name, ItemTargetShape(*item, where.package, scope)},
        item->init_expr, kInner, diag);
  }
}

void ReportMemberParams(const ClassMember& member, const ScopedClass& where,
                        const ParamValueScope& inner, DiagEngine& diag) {
  if (member.method != nullptr)
    ReportProcedureParams(*MethodBody(member.method), inner, where.package,
                          diag);
  if (member.typedef_item != nullptr)
    ReportWrittenSpecialization(member.typedef_item->typedef_type, inner, diag);
  ReportWrittenSpecialization(member.data_type, inner, diag);
  if (!IsParamMember(member)) return;
  ReportIfNotAssignable(
      {member.name, MemberTargetShape(member, where.package, inner)},
      member.init_expr, inner, diag);
}

void ReportClassParams(const ScopedClass& where, const ParamValueScope& outer,
                       DiagEngine& diag) {
  const ClassDecl& cls = where.cls;
  const ParamValueScope kInner{outer.tables, outer.constants, outer.unit,
                               ClassParamShapes(where, outer, WholeClass(cls))};
  for (std::size_t i = 0; i < cls.params.size(); ++i) {
    ReportIfNotAssignable(
        {cls.params[i].first, ClassPortTargetShape(where, i, outer)},
        cls.params[i].second, kInner, diag);
  }
  for (const ClassMember* member : cls.members)
    ReportMemberParams(*member, where, kInner, diag);
  if (const ClassDecl* base = FindBaseClass(&cls, outer.unit))
    ReportSpecializationArgs(InDeclaringScope(*base, outer.unit),
                             cls.base_class_type_params, kInner, diag);
}

}  // namespace

void ReportOverrideNotAssignable(const RtlirParamDecl& pd,
                                 const ParamValueScope& target,
                                 const ParamValueWriter& writer,
                                 DiagEngine& diag) {
  static const RtlirModule kNoModule{};
  const RtlirModule& module =
      writer.module != nullptr ? *writer.module : kNoModule;
  std::vector<std::string_view> untyped_names;
  const ParamValueScope kWriter{target.tables, writer.constants, target.unit};
  const ParamValueScope kValues{
      target.tables, writer.constants, target.unit,
      ModuleScopeShapes(
          {{module, writer.prefix}, untyped_names, module.params.size()},
          kWriter)};
  ReportIfNotAssignable({pd.name, ParamDeclTargetShape(pd, target)},
                        writer.value, kValues, diag);
}

void RecordParamDefaultMismatches(RtlirModule& mod, std::size_t first,
                                  const ParamValueScope& scope, Arena& arena) {
  for (std::size_t i = first; i < mod.params.size(); ++i) {
    RtlirParamDecl& pd = mod.params[i];
    if (pd.from_override) continue;
    std::vector<std::string_view> untyped_names;
    const ParamValueScope kInner{
        scope.tables, scope.constants, scope.unit,
        ModuleScopeShapes({{mod, pd.gen_block_prefix}, untyped_names, i},
                          scope)};
    if (ValueAssignable(ParamDeclTargetShape(pd, scope), pd.default_value,
                        kInner))
      continue;
    pd.default_mismatch =
        arena.Create<ParamDefaultMismatch>(ParamDefaultMismatch{
            pd.default_value->range.start, std::move(untyped_names)});
  }
}

void ReportParamDefaultMismatches(const RtlirModule& mod, DiagEngine& diag) {
  for (const RtlirParamDecl& pd : mod.params) {
    if (pd.default_mismatch == nullptr || pd.from_override) continue;
    if (std::ranges::any_of(pd.default_mismatch->untyped_names,
                            [&mod](std::string_view name) {
                              return OverriddenByName(mod.params, name);
                            }))
      continue;
    ReportNotAssignable(pd.name, pd.default_mismatch->loc, diag);
  }
  for (const RtlirModuleInst& child : mod.children) {
    if (child.resolved != nullptr)
      ReportParamDefaultMismatches(*child.resolved, diag);
  }
}

void ReportProcedureParamValueTypes(const ModuleItem& item,
                                    const ParamModuleSite& site,
                                    const ParamValueScope& scope,
                                    DiagEngine& diag) {
  std::vector<std::string_view> untyped_names;
  const ParamValueScope kOuter{
      scope.tables, scope.constants, scope.unit,
      ModuleScopeShapes({site, untyped_names, site.module.params.size()},
                        scope)};
  ReportProcedureParams(item, kOuter, nullptr, diag);
}

void ReportUnitParamValueTypes(const ParamValueScope& scope, DiagEngine& diag) {
  ReportItemParams({scope.unit->cu_items, nullptr}, scope, diag);
  for (const PackageDecl* pkg : scope.unit->packages)
    ReportItemParams({pkg->items, pkg}, scope, diag);
  for (const ClassScope& where : DeclaredClassScopes(scope.unit)) {
    for (const ClassDecl* cls : where.classes) {
      const ScopedClass kClass = InDeclaringScope(*cls, scope.unit);
      const ParamValueScope kOuter{
          scope.tables, scope.constants, scope.unit,
          ItemParamShapes({*where.items, kClass.package}, scope)};
      ReportClassParams(kClass, kOuter, diag);
    }
  }
}

void ReportSpecializationValueTypes(const DataType& type,
                                    const ParamModuleSite& site,
                                    const ParamValueScope& scope,
                                    DiagEngine& diag) {
  std::vector<std::string_view> untyped_names;
  const ParamValueScope kOuter{
      scope.tables, scope.constants, scope.unit,
      ModuleScopeShapes({site, untyped_names, site.module.params.size()},
                        scope)};
  ReportWrittenSpecialization(type, kOuter, diag);
}

}  // namespace delta
