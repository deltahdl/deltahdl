#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <functional>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/net_or_variable_type.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_enum_member.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_site_lookup.h"
#include "elaborator/unit_scope_order.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

// The value parameter of `mod` written `name`, or null where none is. A type
// parameter is a type rather than a value, and is left to the name's reading
// as a type.
static const RtlirParamDecl* ValueParamNamed(const RtlirModule* mod,
                                             std::string_view name) {
  for (const auto& p : mod->params) {
    if (p.name == name && !p.is_type_param) return &p;
  }
  return nullptr;
}

namespace {

// The width and signing of a value a type reference's expression names.
struct ValueShape {
  uint32_t width = 0;
  bool is_signed = false;
};

// The shape of the value a name stands for in the scope an expression is
// written in, empty where the scope declares no value of the name.
using ValueShapeOf = std::function<std::optional<ValueShape>(std::string_view)>;

// What a type reference's argument is looked up in beyond the module's own
// variables and nets: the module, the typedefs in force, the compilation unit
// and the position of the declaration writing the reference, with the arena a
// resolved type's packed dimensions are made in, and the declaration of the
// module being elaborated, the last of Elaborator::module_decl_path_, within
// whose elaboration every type reference is resolved.
struct TypeRefScope {
  const RtlirModule* mod;
  const TypedefMap& typedefs;
  const CompilationUnit* unit;
  SourceLoc reference;
  Arena& arena;
  const ModuleDecl* decl;
};

}  // namespace

// The shape of the value `name` stands for in `mod`: a variable's, a net's,
// or a value parameter's, which §6.20.2 makes as wide as its declaration, or
// as its final value where it was declared with neither range nor type.
// Empty where `name` is none of them.
static std::optional<ValueShape> NamedValueShape(std::string_view name,
                                                 const RtlirModule* mod) {
  for (const auto& v : mod->variables) {
    if (v.name == name) return ValueShape{v.width, v.is_signed};
  }
  for (const auto& n : mod->nets) {
    if (n.name == name) return ValueShape{n.width, n.is_signed};
  }
  if (const RtlirParamDecl* pd = ValueParamNamed(mod, name)) {
    ParamStorageShape shape = ParamStorageShapeOf(*pd);
    return ValueShape{shape.width, shape.is_signed};
  }
  return std::nullopt;
}

// The values in scope of a module: its variables, nets and value parameters
// (NamedValueShape).
static ValueShapeOf ShapesIn(const RtlirModule* mod) {
  return [mod](std::string_view name) { return NamedValueShape(name, mod); };
}

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
static void SetTypeRefPackedDims(DataType& dt, uint32_t width, Arena& arena) {
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

void AdoptReferencedType(DataType& dt, const DataType& type) {
  dt.kind = type.kind;
  dt.is_signed = type.is_signed;
  dt.type_name = type.type_name;
  dt.packed_dim_left = type.packed_dim_left;
  dt.packed_dim_right = type.packed_dim_right;
  dt.extra_packed_dims = type.extra_packed_dims;
  dt.type_ref_expr = nullptr;
}

// Takes onto `dt`, in place of its type reference, the logic vector of
// `shape`'s width and signing.
static void AdoptLogicVector(DataType& dt, ValueShape shape, Arena& arena) {
  dt.kind = DataTypeKind::kLogic;
  dt.is_signed = shape.is_signed;
  SetTypeRefPackedDims(dt, shape.width, arena);
  dt.type_ref_expr = nullptr;
}

// §6.23: takes onto `dt`, in place of its type reference, the self-determined
// type `type` of the expression the reference names: a structure, union or
// enumeration whole, keeping the declaration's own `const`, and any other type
// as AdoptReferencedType takes it. A logic bit where the expression is of no
// type a data type alone carries.
static void AdoptExpressionType(DataType& dt,
                                const std::optional<DataType>& type,
                                Arena& arena) {
  if (!type) {
    AdoptLogicVector(dt, {}, arena);
    return;
  }
  if (type->struct_members.empty() && type->enum_members.empty()) {
    AdoptReferencedType(dt, *type);
    return;
  }
  bool is_const = dt.is_const;
  dt = *type;
  dt.is_const = is_const;
  dt.type_ref_expr = nullptr;
}

// The item of `items` written `name`, or null where none is.
static const ModuleItem* ItemNamed(std::span<ModuleItem* const> items,
                                   std::string_view name) {
  auto it = std::ranges::find(items, name, &ModuleItem::name);
  return it == items.end() ? nullptr : *it;
}

// The first package of `unit` that `reaches` answers true for and that
// declares an item written `name`, or null where none does.
static const PackageDecl* PackageDeclaring(
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
static DataType DeclaredValueType(const ModuleItem& item,
                                  const ValueShapeOf& shape_of, Arena& arena) {
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

static std::optional<ValueShape> ScopeValueShape(
    std::string_view name, std::span<ModuleItem* const> items, Arena& arena);

// §6.20.2 with §26.2 and §3.12.1: the type of the value `item` declares among
// `items`, the declarations of a package or of the compilation unit. A
// parameter of no type takes its value's, whose names are those `items`
// declares ahead of the parameter (ScopeValueShape).
static DataType ScopeValueType(const ModuleItem& item,
                               std::span<ModuleItem* const> items,
                               Arena& arena) {
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
static std::optional<ValueShape> EnumConstantShape(
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
static std::optional<ValueShape> ScopeValueShape(
    std::string_view name, std::span<ModuleItem* const> items, Arena& arena) {
  auto param = std::ranges::find_if(items, [&](const ModuleItem* i) {
    return i->kind == ModuleItemKind::kParamDecl && i->name == name;
  });
  if (param == items.end()) return EnumConstantShape(name, items);
  DataType type = ScopeValueType(**param, items, arena);
  return ValueShape{EvalTypeWidth(type), type.is_signed};
}

// The type of the value `name` that the module's declaration writes: a port's,
// or that of a variable, net or parameter of its body. A type reference reads
// it there where the module has yet to elaborate the value, as a port's does,
// the ports being elaborated ahead of the items (Elaborator::ElaboratePorts).
// Nothing where the declaration writes nothing of the name.
static std::optional<DataType> ModuleValueType(std::string_view name,
                                               const TypeRefScope& scope) {
  const auto& ports = scope.decl->ports;
  auto port = std::ranges::find(ports, name, &PortDecl::name);
  if (port != ports.end()) return port->data_type;
  const ModuleItem* item = ItemNamed(scope.decl->items, name);
  if (item == nullptr) return std::nullopt;
  return DeclaredValueType(*item, ShapesIn(scope.mod), scope.arena);
}

// §26.3 with §3.12.1: the type of the value `name` names outside the module,
// read in the scope declaring it (ScopeValueType): one a package the module
// imports it from declares, or else one of the compilation unit written before
// the reference. Nothing where neither is.
static std::optional<DataType> OuterValueType(std::string_view name,
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

// §6.19: the named constant `name` of an enumeration the module sees, or null
// where no enumeration declares it, with the key RtlirModule::enum_types
// holds that enumeration under.
static const RtlirEnumMember* EnumConstantNamed(const RtlirModule* mod,
                                                std::string_view name,
                                                std::string_view& key) {
  for (const auto& [enum_key, members] : mod->enum_types) {
    auto it = std::ranges::find(members, name, &RtlirEnumMember::name);
    if (it == members.end()) continue;
    key = enum_key;
    return &*it;
  }
  return nullptr;
}

// §6.19.3 with §6.23: the enumerated type declaring `constant`, keyed `key`,
// which a type reference to the constant stands for. A typedef's enumeration
// is named by the typedef, and the declaration resolves the name as it would
// a typedef it wrote. One written as a variable's or a structure member's type
// has no name another declaration could write, so the declaration takes a
// copy of it, keeping its own `const`, and the key is answered: the
// declaration declares none of the enumeration's constants again, and names
// its enumeration by the key. Empty for a typedef's.
static std::string_view AdoptEnumerationType(DataType& dt,
                                             const RtlirEnumMember& constant,
                                             std::string_view key,
                                             const TypeRefScope& scope) {
  if (scope.typedefs.count(key) != 0) {
    AdoptReferencedType(dt, TypeNameToDataType(key));
    return {};
  }
  bool is_const = dt.is_const;
  dt = *constant.enumeration;
  dt.is_const = is_const;
  return key;
}

// §6.23 with §7.2: takes onto each member of the structure or union `dt`
// whose type is a type reference, `struct { type(x) f; }`, the type the
// reference stands for, which `resolve` resolves in place, as the parser takes
// a written member type onto its member (ApplyMemberType). The whole type is
// kept as the member's nested type, which its width, its state and its layout
// are read from.
static void ResolveMemberTypeRefs(
    DataType& dt, Arena& arena, const std::function<void(DataType&)>& resolve) {
  for (StructMember& m : dt.struct_members) {
    if (m.nested_type == nullptr || m.nested_type->type_ref_expr == nullptr) {
      continue;
    }
    DataType type = *m.nested_type;
    resolve(type);
    m.type_kind = type.kind;
    m.is_signed = type.is_signed;
    m.packed_dim_left = type.packed_dim_left;
    m.packed_dim_right = type.packed_dim_right;
    m.extra_packed_dims = type.extra_packed_dims;
    m.type_name = type.type_name;
    m.scope_name = type.scope_name;
    m.nested_type = arena.Create<DataType>(type);
  }
}

// §8.23 names the type operator as a context in which a class scope resolution
// may prefix a type name, so `type(Frame::payload_t)` denotes the typedef
// `payload_t` declared in class `Frame`, and §26.3 lets a package's scope
// prefix the name of a value it declares, so `type(p::W)` stands for the type
// of package `p`'s W. Either parses to a kMemberAccess node, which
// ResolveTypeRef would otherwise treat as an expression whose width and
// signedness are unknown, making the declared object a 1-bit unsigned logic.
// Returns false, leaving `dt` untouched, when `ref` is not a scope resolution
// over two identifiers or when neither a class's typedef nor a package's
// declaration is found by it.
static bool ResolveScopedTypeRef(DataType& dt, const Expr* ref,
                                 const TypeRefScope& scope) {
  if (ref->kind != ExprKind::kMemberAccess || !ref->is_scope_resolution) {
    return false;
  }
  if (ref->lhs == nullptr || ref->lhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  if (ref->rhs == nullptr || ref->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  std::string_view prefix = ref->lhs->text;
  if (const DataType* resolved =
          FindClassScopedTypedefType(prefix, ref->rhs->text, scope.unit)) {
    AdoptReferencedType(dt, *resolved);
    return true;
  }
  const PackageDecl* pkg = PackageDeclaring(
      scope.unit, ref->rhs->text,
      [&](std::string_view package) { return package == prefix; });
  if (pkg == nullptr) return false;
  AdoptReferencedType(dt, ScopeValueType(*ItemNamed(pkg->items, ref->rhs->text),
                                         pkg->items, scope.arena));
  return true;
}

// §6.23 with §6.20.2: a type reference whose argument is a name no variable or
// net of the module carries. A parameter stands for its type: the one it was
// declared with, or, declared with no type, the logic vector of its declared
// range or of its final value. A built-in type keyword and a typedef name,
// which the parser reads as identifiers, stand for the type they spell, a
// typedef's left named for the declaration's own resolution of it. A value of a
// package or of the compilation unit stands for its type (OuterValueType). A
// name that is none of these leaves the reference as it stands, for the scope
// rules to report.
static void ResolveNamedTypeRef(DataType& dt, std::string_view name,
                                const TypeRefScope& scope) {
  if (const RtlirParamDecl* pd = ValueParamNamed(scope.mod, name)) {
    if (pd->decl_type != nullptr && !pd->decl_type_implicit) {
      AdoptReferencedType(dt, *pd->decl_type);
      return;
    }
    ParamStorageShape shape = ParamStorageShapeOf(*pd);
    AdoptLogicVector(dt, {shape.width, shape.is_signed}, scope.arena);
    return;
  }
  DataType spelled = TypeNameToDataType(name);
  if (spelled.kind != DataTypeKind::kNamed || scope.typedefs.count(name) != 0) {
    AdoptReferencedType(dt, spelled);
    return;
  }
  if (std::optional<DataType> own = ModuleValueType(name, scope)) {
    AdoptReferencedType(dt, *own);
    return;
  }
  if (std::optional<DataType> outer = OuterValueType(name, scope)) {
    AdoptReferencedType(dt, *outer);
  }
}

// §6.23: the type a net or variable `name` of `mod` stands for where no
// declaration records the data type it is declared with: a variable's recorded
// kind, as wide as the variable where that kind is a vector's, or the logic
// vector of a net's width. False, leaving `dt` untouched, where `mod` holds no
// value of that name.
static bool AdoptRecordedValueType(
    DataType& dt, std::string_view name, const RtlirModule& mod,
    std::unordered_map<std::string_view, DataTypeKind>& var_types,
    Arena& arena) {
  for (const auto& v : mod.variables) {
    if (v.name != name) continue;
    dt.kind = var_types[name];
    dt.is_signed = v.is_signed;
    if (dt.kind == DataTypeKind::kLogic || dt.kind == DataTypeKind::kBit ||
        dt.kind == DataTypeKind::kReg) {
      SetTypeRefPackedDims(dt, v.width, arena);
    }
    dt.type_ref_expr = nullptr;
    return true;
  }
  // §6.23: type(net) yields the net's underlying data type (a logic vector of
  // the net's width); the net-ness of the declared object comes separately from
  // its own net keyword, not from the type_reference.
  for (const auto& n : mod.nets) {
    if (n.name != name) continue;
    AdoptLogicVector(dt, {n.width, n.is_signed}, arena);
    return true;
  }
  auto it = var_types.find(name);
  if (it == var_types.end()) return false;
  dt.kind = it->second;
  dt.type_ref_expr = nullptr;
  return true;
}

// §6.23: resolves the type reference `dt` holds, if any, written at `loc` in
// `mod`, to the type it stands for, in place. Answers the key
// RtlirModule::enum_types holds an enumeration under where the reference
// named a constant of one no typedef names, whose type `dt` then copies
// (AdoptEnumerationType), and empty otherwise.
std::string_view Elaborator::ResolveTypeRef(DataType& dt, SourceLoc loc,
                                            const RtlirModule* mod) {
  ResolveMemberTypeRefs(
      dt, arena_, [&](DataType& type) { ResolveTypeRef(type, loc, mod); });
  if (!dt.type_ref_expr) return {};
  auto* ref = dt.type_ref_expr;
  CheckTypeRefArgInner(ref, loc);
  const ModuleDecl* decl = module_decl_path_.back();
  const TypeRefScope kScope{mod, typedefs_, unit_, loc, arena_, decl};
  if (ResolveScopedTypeRef(dt, ref, kScope)) return {};
  if (std::optional<DataType> returned = CalledFunctionType(ref)) {
    AdoptReferencedType(dt, *returned);
    return {};
  }
  if (ref->kind != ExprKind::kIdentifier) {
    AdoptExpressionType(dt, TypeRefExprType(ref, mod), arena_);
    return {};
  }
  // A named constant of an enumeration stands for the enumeration's type. It
  // is looked up before the module's variables, which BuildEnumMembers gives
  // each constant one of to hold its value: matched there, the constant read
  // var_types_, which records no such name, and took the implicit type's one
  // bit.
  std::string_view enumeration;
  if (const RtlirEnumMember* constant =
          EnumConstantNamed(mod, ref->text, enumeration)) {
    return AdoptEnumerationType(dt, *constant, enumeration, kScope);
  }
  // §6.23 with §6.22.1 (f): a net or variable stands for the type it is
  // declared with, range and all, which one rebuilt from its width as
  // [width-1:0] is not where the declaration writes [0:3].
  if (std::optional<DataType> declared = NetOrVariableType(
          *mod,
          DeclaredScopedName(ref->text, gen_prefix_scopes_, declared_names_))) {
    AdoptReferencedType(dt, *declared);
    return {};
  }
  if (AdoptRecordedValueType(dt, ref->text, *mod, var_types_, arena_)) {
    return {};
  }
  ResolveNamedTypeRef(dt, ref->text, kScope);
  return {};
}

void ResolveScopeTypeRef(DataType& dt, const std::vector<ModuleItem*>& items,
                         Arena& arena) {
  const Expr* ref = dt.type_ref_expr;
  if (ref == nullptr || ref->kind != ExprKind::kIdentifier) return;
  DataType spelled = TypeNameToDataType(ref->text);
  const ModuleItem* item = ItemNamed(items, ref->text);
  if (spelled.kind != DataTypeKind::kNamed ||
      (item != nullptr && item->kind == ModuleItemKind::kTypedef)) {
    AdoptReferencedType(dt, spelled);
    return;
  }
  if (item == nullptr) return;
  AdoptReferencedType(dt, ScopeValueType(*item, items, arena));
}

// The class a name reaches, or nothing when the answer is not clear.
//
// §8.1 lets a class be declared wherever a data declaration may appear, so the
// compilation unit's own list holds only the ones written at the top of a file
// and a lookup confined to it cannot see a class declared inside a module. What
// it must not do instead is guess: two modules may each declare a class of one
// name, and answering with whichever came first would resolve a rule against a
// class the source never named -- a wrong answer where there had only been
// silence. So a name declared once among the scopes is resolved, a name
// declared in more than one is left unresolved, and the caller is no worse off
// than it was.
static const ClassDecl* FindClassAmong(std::string_view name,
                                       const std::vector<ModuleItem*>& items) {
  for (const auto* item : items) {
    if (item != nullptr && item->kind == ModuleItemKind::kClassDecl &&
        item->class_decl != nullptr && item->class_decl->name == name) {
      return item->class_decl;
    }
  }
  return nullptr;
}

static void TakeUniqueMatch(const ClassDecl* found, const ClassDecl*& only,
                            bool& ambiguous) {
  if (found == nullptr) return;
  if (only != nullptr) ambiguous = true;
  only = found;
}

const ClassDecl* FindClassDecl(std::string_view name,
                               const CompilationUnit* unit) {
  for (const auto* cls : unit->classes) {
    if (cls->name == name) return cls;
  }
  const ClassDecl* only = nullptr;
  bool ambiguous = false;
  for (const auto* group :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const auto* decl : *group) {
      TakeUniqueMatch(FindClassAmong(name, decl->items), only, ambiguous);
    }
  }
  for (const auto* pkg : unit->packages) {
    TakeUniqueMatch(FindClassAmong(name, pkg->items), only, ambiguous);
  }
  return ambiguous ? nullptr : only;
}

// The site of the scope among `items`, of kind `kind`, that declares `cls`
// directly; `found` is left alone where `items` does not.
static void TakeDeclaringSite(const ClassDecl* cls,
                              const std::vector<ModuleItem*>& items,
                              SiteKind kind, TypeSite& found) {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kClassDecl && item->class_decl == cls) {
      found = TypeSite{&items, items.size(), kind};
    }
  }
}

const ClassDecl* FindBaseClass(const ClassDecl* cls,
                               const CompilationUnit* unit) {
  if (cls->base_class.empty()) return nullptr;
  const ClassDecl* in_package =
      FindClassInPackage(cls->base_class_scope, cls->base_class, unit);
  if (in_package != nullptr) return in_package;
  TypeSite site;
  TakeDeclaringSite(cls, unit->cu_items, SiteKind::kUnit, site);
  for (const auto* group :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const auto* decl : *group) {
      TakeDeclaringSite(cls, decl->items, SiteKind::kModule, site);
    }
  }
  for (const auto* pkg : unit->packages) {
    TakeDeclaringSite(cls, pkg->items, SiteKind::kPackage, site);
  }
  const ClassDecl* seen =
      site.items == nullptr ? nullptr : ClassIn(*unit, site, cls->base_class);
  return seen != nullptr ? seen : FindClassDecl(cls->base_class, unit);
}

// Appends `cls` and, after it, each class nested in its body (§8.23), which
// the parser keeps as a kClassDecl member rather than in any scope's list.
static void AppendClassAndNested(const ClassDecl* cls,
                                 std::vector<const ClassDecl*>& out) {
  out.push_back(cls);
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kClassDecl && m->nested_class != nullptr)
      AppendClassAndNested(m->nested_class, out);
  }
}

static void AppendClassDecls(const std::vector<ModuleItem*>& items,
                             std::vector<const ClassDecl*>& out);

// Appends the classes of the generate blocks a generate construct holds: a
// loop's or a branch's own block, the else branch chained after it, and each
// case item's block.
static void AppendGenerateClassDecls(const ModuleItem* item,
                                     std::vector<const ClassDecl*>& out) {
  for (; item != nullptr; item = item->gen_else) {
    AppendClassDecls(item->gen_body, out);
    for (const auto& case_item : item->gen_case_items) {
      AppendClassDecls(case_item.body, out);
    }
  }
}

// Appends the classes declared among `items`, with those of every generate
// block the items hold, since A.1.11 makes class_declaration a
// package_or_generate_item_declaration.
static void AppendClassDecls(const std::vector<ModuleItem*>& items,
                             std::vector<const ClassDecl*>& out) {
  for (const auto* item : items) {
    if (item == nullptr) continue;
    if (item->kind == ModuleItemKind::kClassDecl &&
        item->class_decl != nullptr) {
      AppendClassAndNested(item->class_decl, out);
    }
    AppendGenerateClassDecls(item, out);
  }
}

std::vector<const ClassDecl*> AllClassDecls(const CompilationUnit* unit) {
  std::vector<const ClassDecl*> out;
  for (const auto* cls : unit->classes) AppendClassAndNested(cls, out);
  for (const auto* group :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const auto* decl : *group) AppendClassDecls(decl->items, out);
  }
  for (const auto* pkg : unit->packages) AppendClassDecls(pkg->items, out);
  return out;
}

std::string_view NestedClassKey(const DataType& dtype,
                                const CompilationUnit* unit, Arena& arena) {
  if (dtype.kind != DataTypeKind::kNamed || dtype.scope_name.empty()) return {};
  const ClassDecl* outer = FindClassDecl(dtype.scope_name, unit);
  if (outer == nullptr) return {};
  for (const auto* m : outer->members) {
    if (m->kind != ClassMemberKind::kClassDecl || m->name != dtype.type_name)
      continue;
    return *arena.Create<std::string>(std::string(dtype.scope_name) +
                                      "::" + std::string(dtype.type_name));
  }
  return {};
}

std::string_view PackageClassKey(const DataType& dtype,
                                 const TypedefMap& typedefs,
                                 const CompilationUnit* unit, Arena& arena) {
  if (dtype.kind != DataTypeKind::kNamed || dtype.scope_name.empty()) return {};
  // §6.18: a typedef stands for the name its chain ends at, which the
  // package's own typedefs leave bare (InPackageScope) and which a typedef of
  // another package's class writes behind that package.
  DataType end = LastTypeInChain(dtype, typedefs);
  if (end.scope_name.empty()) end.scope_name = dtype.scope_name;
  for (const auto* pkg : unit->packages) {
    if (pkg->name != end.scope_name) continue;
    for (const auto* item : pkg->items) {
      if (item->kind != ModuleItemKind::kClassDecl || !item->class_decl ||
          item->class_decl->name != end.type_name)
        continue;
      return *arena.Create<std::string>(std::string(end.scope_name) +
                                        "::" + std::string(end.type_name));
    }
  }
  return {};
}

static const ModuleItem* FindClassTypedef(const ClassDecl* cls,
                                          std::string_view member_name) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kTypedef && m->name == member_name) {
      return m->typedef_item;
    }
  }
  return nullptr;
}

const ModuleItem* FindClassScopedTypedefItem(std::string_view cls_name,
                                             std::string_view type_name,
                                             const CompilationUnit* unit) {
  const auto* cls = FindClassDecl(cls_name, unit);
  if (cls == nullptr) return nullptr;
  return FindClassTypedef(cls, type_name);
}

const DataType* FindClassScopedTypedefType(std::string_view cls_name,
                                           std::string_view type_name,
                                           const CompilationUnit* unit) {
  const ModuleItem* td = FindClassScopedTypedefItem(cls_name, type_name, unit);
  if (td == nullptr) return nullptr;
  return &td->typedef_type;
}

// Both functions below ask whether a scope-qualified name's key
// (TypeChainKey, which FindNamedType looks it up by) is present before
// reaching for a class, and reach for it through every prefix written before
// the scope (ClassOfChainedScope), §8.23 naming a nested class by the whole
// chain. Keyed and found by the last prefix alone, `Outer::Inner::u` was
// judged against the compilation unit's own class Inner, which declares no u.
bool ResolveClassScopedDeclType(DataType& dtype, const TypedefMap& typedefs,
                                const CompilationUnit* unit) {
  if (dtype.kind != DataTypeKind::kNamed || dtype.scope_name.empty()) {
    return false;
  }
  if (typedefs.count(TypeChainKey(dtype)) > 0) return false;
  const ClassDecl* cls = ClassOfChainedScope(dtype, unit);
  if (cls == nullptr) return false;
  const ModuleItem* td = FindClassTypedef(cls, dtype.type_name);
  if (td == nullptr) return false;
  const DataType& resolved = td->typedef_type;
  dtype.kind = resolved.kind;
  dtype.is_signed = resolved.is_signed;
  dtype.type_name = resolved.type_name;
  dtype.packed_dim_left = resolved.packed_dim_left;
  dtype.packed_dim_right = resolved.packed_dim_right;
  dtype.extra_packed_dims = resolved.extra_packed_dims;
  return true;
}

// Whether `cls` declares anything at all under `name`. §8.23 puts a nested
// class declaration and a typedef in one list -- the class scope resolution
// operator reaches every static element of a class, its static properties,
// static methods, typedefs, enumerations, parameters, local parameters,
// constraints, structures, unions and nested class declarations -- so a name
// this tool does not resolve to a type is still a name the class declared, and
// `StringList::Node n;` is the case that is.
static bool ClassDeclaresMember(const ClassDecl* cls, std::string_view name) {
  for (const auto* m : cls->members) {
    if (m->name == name) return true;
  }
  return false;
}

void ReportUnresolvedClassScopedType(const DataType& dtype, SourceLoc loc,
                                     const TypedefMap& typedefs,
                                     const CompilationUnit* unit,
                                     DiagEngine& diag) {
  if (dtype.kind != DataTypeKind::kNamed || dtype.scope_name.empty()) return;
  if (!dtype.type_params.empty()) return;
  if (typedefs.count(TypeChainKey(dtype)) > 0) return;
  const ClassDecl* cls = ClassOfChainedScope(dtype, unit);
  if (cls == nullptr) return;
  if (!cls->base_class.empty() || !cls->extends_interfaces.empty()) return;
  if (cls->members.empty()) return;
  if (ClassDeclaresMember(cls, dtype.type_name)) return;
  diag.Error(loc,
             std::format("class '{}' declares no type '{}'", dtype.scope_name,
                         dtype.type_name),
             Subclause("8.23"));
}

// What each parameter of `cls` stands for in the specialization `args` writes,
// keyed by the parameter's own name.
//
// §23.10.2.2 (printed page 767) makes a parameter assignment by name an
// explicit pairing of the parameter's name with its new value, so a written
// name selects the formal whatever position the argument holds, and an argument
// written without one takes the position it holds. The same subclause requires
// only the parameters given new values to be named, not all of them, so a
// formal the list does not mention keeps the default its declaration gave,
// which ClassDecl::param_types records. §8.25 (printed page 204) instantiates a
// specialization by the parameter override rules of §23.10, which is what
// brings all three to bear on a specialization.
//
// A formal declared with no default has a kImplicit entry in param_types and is
// left out, so a member reaching it fails to resolve rather than resolving to a
// type nothing named.
static std::unordered_map<std::string_view, const DataType*>
BuildSpecializationSubst(const ClassDecl* cls,
                         const std::vector<DataType>& args) {
  std::unordered_map<std::string_view, const DataType*> subst;
  for (size_t i = 0; i < args.size(); ++i) {
    if (!args[i].param_arg_name.empty()) {
      subst[args[i].param_arg_name] = &args[i];
    } else if (i < cls->params.size()) {
      subst[cls->params[i].first] = &args[i];
    }
  }
  size_t defaults = std::min(cls->params.size(), cls->param_types.size());
  for (size_t i = 0; i < defaults; ++i) {
    if (cls->param_types[i].kind == DataTypeKind::kImplicit) continue;
    subst.emplace(cls->params[i].first, &cls->param_types[i]);
  }
  return subst;
}

// Reports a named argument of a specialization carrying a name the class does
// not declare, and one assigning a name a second argument already assigned.
//
// §23.10.2.2 (printed page 767) requires the parameter name to be the one the
// instantiated module specifies, and forbids a second assignment to a parameter
// name once it has a value. §8.25 (printed page 204) instantiates a
// specialization by the parameter override rules of §23.10. Neither report
// changes what BuildSpecializationSubst goes on to substitute: an unrecognized
// name binds no parameter, so the one it was written for keeps its declared
// default, and a repeated name leaves the last argument standing. Both of those
// are types nobody wrote, which is what the reports stand in place of.
//
// ResolveNamedInstParams in src/elaborator/elaborator_module_inst.cpp makes
// the first of these reports for a module instance, and the wording here
// follows it so that the two forms of one rule read alike.
static void ValidateSpecializationArgNames(const ClassDecl* cls,
                                           const std::vector<DataType>& args,
                                           DiagEngine& diag, SourceLoc loc) {
  std::unordered_set<std::string_view> declared;
  for (const auto& [pname, pexpr] : cls->params) declared.insert(pname);
  std::unordered_set<std::string_view> assigned;
  for (const auto& arg : args) {
    if (arg.param_arg_name.empty()) continue;
    if (declared.count(arg.param_arg_name) == 0) {
      diag.Error(loc,
                 std::format("class '{}' has no parameter '{}'", cls->name,
                             arg.param_arg_name),
                 Subclause("23.10.2.2"));
    } else if (!assigned.insert(arg.param_arg_name).second) {
      diag.Error(loc,
                 std::format("parameter '{}' of class '{}' is assigned more "
                             "than once",
                             arg.param_arg_name, cls->name),
                 Subclause("23.10.2.2"));
    }
  }
}

bool ResolveParameterizedType(DataType& dtype, const CompilationUnit* unit,
                              DiagEngine& diag, SourceLoc loc) {
  if (dtype.scope_name.empty() || dtype.type_params.empty()) return false;
  const auto* cls = FindClassDecl(dtype.scope_name, unit);
  if (!cls) return false;
  ValidateSpecializationArgNames(cls, dtype.type_params, diag, loc);
  auto subst = BuildSpecializationSubst(cls, dtype.type_params);

  // The scope resolution operator applied to a specialization may name a type
  // parameter of the class directly, or a member typedef whose aliased type is
  // one of those parameters. Resolve a direct type-parameter reference first;
  // otherwise look through a member typedef to the parameter it aliases.
  std::string_view param_name = dtype.type_name;
  if (!subst.count(param_name)) {
    const auto* td = FindClassTypedef(cls, dtype.type_name);
    if (!td) return false;
    param_name = td->typedef_type.type_name;
  }
  auto it = subst.find(param_name);
  if (it == subst.end()) return false;
  const DataType& resolved = *it->second;
  dtype.kind = resolved.kind;
  dtype.is_signed = resolved.is_signed;
  dtype.packed_dim_left = resolved.packed_dim_left;
  dtype.packed_dim_right = resolved.packed_dim_right;
  dtype.extra_packed_dims = resolved.extra_packed_dims;
  dtype.type_name = resolved.type_name;
  dtype.scope_name = {};
  dtype.type_params.clear();
  return true;
}

}  // namespace delta
