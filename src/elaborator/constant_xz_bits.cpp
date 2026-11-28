#include "elaborator/constant_xz_bits.h"

#include <algorithm>
#include <cstddef>
#include <string_view>
#include <vector>

#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

constexpr int kMaxConstantHops = 32;

struct Lookup {
  const XzConstantScope& scope;
  int hops;

  [[nodiscard]] Lookup Next() const { return {scope, hops + 1}; }
};

bool IsScopedName(const Expr* e) {
  return e->kind == ExprKind::kMemberAccess && e->is_scope_resolution &&
         e->lhs != nullptr && e->rhs != nullptr &&
         e->lhs->kind == ExprKind::kIdentifier;
}

bool HoldsXZ(const DataType& type, const Expr* value,
             const NamesXzConstant& names, const Lookup& look) {
  return look.hops < kMaxConstantHops &&
         Is4stateType(type, look.scope.typedefs) &&
         ValueReachesXZ(value, names);
}

const PackageDecl* FindPackage(const CompilationUnit* unit,
                               std::string_view name) {
  auto it = std::ranges::find_if(unit->packages, [&](const PackageDecl* pkg) {
    return pkg->name == name;
  });
  return it == unit->packages.end() ? nullptr : *it;
}

const ClassDecl* FindClass(const CompilationUnit* unit, std::string_view name) {
  auto it = std::ranges::find_if(
      unit->classes, [&](const ClassDecl* cls) { return cls->name == name; });
  return it == unit->classes.end() ? nullptr : *it;
}

const ModuleItem* FindParamItem(const std::vector<ModuleItem*>& items,
                                std::string_view name) {
  auto it = std::ranges::find_if(items, [&](const ModuleItem* item) {
    return item->kind == ModuleItemKind::kParamDecl && item->name == name;
  });
  return it == items.end() ? nullptr : *it;
}

bool NameHoldsXZ(const Expr* e, const std::vector<ModuleItem*>& items,
                 const Lookup& look);

bool ParamOfItemsHoldsXZ(std::string_view name,
                         const std::vector<ModuleItem*>& items,
                         const Lookup& look) {
  const ModuleItem* item = FindParamItem(items, name);
  if (item == nullptr) return false;
  const Lookup kNext = look.Next();
  return HoldsXZ(
      item->data_type, item->init_expr,
      [&](const Expr* e) { return NameHoldsXZ(e, items, kNext); }, look);
}

bool ImportedParamHoldsXZ(std::string_view name, const ImportItem& imp,
                          const Lookup& look) {
  if (!imp.is_wildcard && imp.item_name != name) return false;
  const PackageDecl* pkg = FindPackage(look.scope.unit, imp.package_name);
  return pkg != nullptr && ParamOfItemsHoldsXZ(name, pkg->items, look);
}

bool DeclaresClassConstant(const ClassDecl& cls, std::string_view name) {
  return std::ranges::any_of(cls.params,
                             [&](const auto& p) { return p.first == name; }) ||
         std::ranges::any_of(cls.members, [&](const ClassMember* m) {
           return m->kind == ClassMemberKind::kProperty && m->is_param &&
                  m->name == name;
         });
}

bool ClassNameHoldsXZ(std::string_view name, const ClassDecl& cls,
                      const Lookup& look);

bool ClassScopeNameHoldsXZ(const Expr* e, const ClassDecl& cls,
                           const Lookup& look) {
  if (e->kind == ExprKind::kIdentifier && DeclaresClassConstant(cls, e->text)) {
    return ClassNameHoldsXZ(e->text, cls, look);
  }
  return NameHoldsXZ(e, look.scope.unit->cu_items, look);
}

bool ClassNameHoldsXZ(std::string_view name, const ClassDecl& cls,
                      const Lookup& look) {
  const Lookup kNext = look.Next();
  const NamesXzConstant kNames = [&](const Expr* e) {
    return ClassScopeNameHoldsXZ(e, cls, kNext);
  };
  for (size_t i = 0; i < cls.params.size(); ++i) {
    if (cls.params[i].first != name) continue;
    if (cls.type_param_names.contains(name)) return false;
    const DataType kUntyped;
    const DataType& type =
        i < cls.param_types.size() ? cls.param_types[i] : kUntyped;
    return HoldsXZ(type, cls.params[i].second, kNames, look);
  }
  for (const ClassMember* m : cls.members) {
    if (m->kind == ClassMemberKind::kProperty && m->is_param &&
        m->name == name) {
      return HoldsXZ(m->data_type, m->init_expr, kNames, look);
    }
  }
  return false;
}

bool ScopedNameHoldsXZ(const Expr* e, const Lookup& look) {
  std::string_view scope_name = e->lhs->text;
  std::string_view name = e->rhs->text;
  if (scope_name == "$unit") {
    return ParamOfItemsHoldsXZ(name, look.scope.unit->cu_items, look);
  }
  if (const PackageDecl* pkg = FindPackage(look.scope.unit, scope_name)) {
    return ParamOfItemsHoldsXZ(name, pkg->items, look);
  }
  const ClassDecl* cls = FindClass(look.scope.unit, scope_name);
  return cls != nullptr && ClassNameHoldsXZ(name, *cls, look);
}

bool NameHoldsXZ(const Expr* e, const std::vector<ModuleItem*>& items,
                 const Lookup& look) {
  if (IsScopedName(e)) return ScopedNameHoldsXZ(e, look);
  if (e->kind != ExprKind::kIdentifier) return false;
  if (FindParamItem(items, e->text) != nullptr) {
    return ParamOfItemsHoldsXZ(e->text, items, look);
  }
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kImportDecl &&
        ImportedParamHoldsXZ(e->text, item->import_item, look)) {
      return true;
    }
  }
  const std::vector<ModuleItem*>& unit_items = look.scope.unit->cu_items;
  return &items != &unit_items && NameHoldsXZ(e, unit_items, look);
}

const RtlirParamDecl* VisibleValueParam(const RtlirModule& mod,
                                        std::string_view name,
                                        const GenBlockPrefixes& scopes) {
  const RtlirParamDecl* found = nullptr;
  for (const RtlirParamDecl& param : mod.params) {
    if (param.name == name && !param.is_type_param &&
        ParamVisibleFromScopes(param.gen_block_prefix, scopes)) {
      found = &param;
    }
  }
  return found;
}

}  // namespace

bool ValueReachesXZ(const Expr* e, const NamesXzConstant& names_xz_constant) {
  if (e == nullptr) return false;
  if ((e->kind == ExprKind::kIntegerLiteral ||
       e->kind == ExprKind::kUnbasedUnsizedLiteral) &&
      LiteralHasXZ(e->text)) {
    return true;
  }
  if (e->kind == ExprKind::kIdentifier || IsScopedName(e)) {
    return names_xz_constant(e);
  }
  return AnyExprChild(e, [&](const Expr* child) {
    return ValueReachesXZ(child, names_xz_constant);
  });
}

bool ScopeConstantHoldsXZ(const Expr* name,
                          const std::vector<ModuleItem*>& items,
                          const XzConstantScope& scope) {
  return NameHoldsXZ(name, items, {scope, 0});
}

bool ClassConstantHoldsXZ(const Expr* name, const ClassDecl& cls,
                          const XzConstantScope& scope) {
  return ClassScopeNameHoldsXZ(name, cls, {scope, 0});
}

bool ModuleConstantHoldsXZ(const Expr* name, const RtlirModule& mod,
                           const GenBlockPrefixes& scopes,
                           const XzConstantScope& scope) {
  const Lookup kLook{scope, 0};
  if (name->kind == ExprKind::kIdentifier) {
    if (const RtlirParamDecl* param =
            VisibleValueParam(mod, name->text, scopes)) {
      return param->value_has_xz;
    }
    for (const RtlirImport& imp : mod.imports) {
      ImportItem written;
      written.package_name = imp.package_name;
      written.item_name = imp.item_name;
      written.is_wildcard = imp.is_wildcard;
      if (ImportedParamHoldsXZ(name->text, written, kLook)) return true;
    }
  }
  return NameHoldsXZ(name, scope.unit->cu_items, kLook);
}

bool ParamValueHoldsXZ(const RtlirParamDecl& pd, const DataType* declared,
                       const RtlirModule& mod, const ParamValueScopes& scopes,
                       const XzConstantScope& scope) {
  if (pd.is_type_param || pd.is_real_value || pd.is_string_value) return false;
  if (declared != nullptr && !Is4stateType(*declared, scope.typedefs)) {
    return false;
  }
  const Expr* value = pd.from_override ? pd.override_expr : pd.default_value;
  const RtlirModule* names_in = pd.from_override ? pd.override_module : &mod;
  const GenBlockPrefixes& visible =
      pd.from_override ? scopes.instantiating : scopes.own;
  return ValueReachesXZ(value, [&](const Expr* e) {
    return names_in != nullptr &&
           ModuleConstantHoldsXZ(e, *names_in, visible, scope);
  });
}

}  // namespace delta
