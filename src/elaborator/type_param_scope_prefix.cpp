#include "elaborator/type_param_scope_prefix.h"

#include <algorithm>
#include <cstddef>
#include <format>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_param_restriction.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

static bool MayBeClass(const DataType& type,
                       const TypeParamPrefixScope& scope) {
  const DataType* cur = &type;
  for (int depth = 0; depth < 32; ++depth) {
    if (cur->kind != DataTypeKind::kNamed) return false;
    if (!cur->scope_name.empty()) return true;
    if (scope.class_names.contains(cur->type_name)) return true;
    auto next = scope.typedefs.find(cur->type_name);
    if (next == scope.typedefs.end() || &next->second == cur) return true;
    cur = &next->second;
  }
  return true;
}

static void EmitPrefixNotAClass(std::string_view prefix, SourceLoc loc,
                                DiagEngine& diag) {
  diag.ErrorOnce(loc,
                 std::format("type parameter '{}' used as a class scope "
                             "resolution prefix does not resolve to a class",
                             prefix),
                 Subclause("6.20.3"));
}

void ReportTypeParamPrefixNotAClass(std::string_view prefix, SourceLoc loc,
                                    const TypeParamPrefixScope& scope,
                                    DiagEngine& diag) {
  if (prefix.empty()) return;
  bool is_type_param =
      std::ranges::any_of(scope.params, [&](const RtlirParamDecl& p) {
        return p.is_type_param && p.name == prefix;
      });
  if (!is_type_param) return;
  auto bound = scope.typedefs.find(prefix);
  if (bound == scope.typedefs.end() || MayBeClass(bound->second, scope)) return;
  EmitPrefixNotAClass(prefix, loc, diag);
}

namespace {

struct LocalTypeName {
  std::string_view name;
  const DataType* bound;
  bool is_param;
};

using LocalTypeNames = std::vector<LocalTypeName>;

struct PrefixWalk {
  const TypeParamPrefixScope* outer;
  const TypeParamRestrictionScope& restriction;
  DiagEngine& diag;
  bool outer_type_refs = false;
};

const LocalTypeName* FindLocal(const LocalTypeNames& locals,
                               std::string_view name) {
  for (auto it = locals.rbegin(); it != locals.rend(); ++it) {
    if (it->name == name) return &*it;
  }
  return nullptr;
}

bool BoundToNoClass(const LocalTypeName& local, const LocalTypeNames& locals) {
  const DataType* cur = local.bound;
  for (int depth = 0; depth < 32; ++depth) {
    if (cur->kind == DataTypeKind::kImplicit) return false;
    if (cur->kind != DataTypeKind::kNamed) return true;
    if (!cur->scope_name.empty()) return false;
    const LocalTypeName* next = FindLocal(locals, cur->type_name);
    if (next == nullptr || next->bound == cur) return false;
    cur = next->bound;
  }
  return false;
}

void JudgePrefix(std::string_view prefix, SourceLoc loc,
                 const LocalTypeNames& locals, const PrefixWalk& walk,
                 bool outer_too) {
  if (prefix.empty()) return;
  if (const LocalTypeName* local = FindLocal(locals, prefix)) {
    if (local->is_param && BoundToNoClass(*local, locals))
      EmitPrefixNotAClass(prefix, loc, walk.diag);
    return;
  }
  if (outer_too && walk.outer != nullptr)
    ReportTypeParamPrefixNotAClass(prefix, loc, *walk.outer, walk.diag);
}

std::string_view TypeRefPrefix(const DataType& type) {
  const Expr* ref = type.type_ref_expr;
  if (ref == nullptr || ref->kind != ExprKind::kMemberAccess ||
      !ref->is_scope_resolution || ref->lhs == nullptr ||
      ref->lhs->kind != ExprKind::kIdentifier)
    return {};
  return ref->lhs->text;
}

void JudgeTypeRef(const DataType& type, SourceLoc loc,
                  const LocalTypeNames& locals, const PrefixWalk& walk) {
  JudgePrefix(TypeRefPrefix(type), loc, locals, walk, walk.outer_type_refs);
}

bool NamesLocal(const DataType& type, const LocalTypeName& local) {
  return type.kind == DataTypeKind::kNamed && type.scope_name.empty() &&
         type.type_name == local.name;
}

void JudgeRestriction(const ModuleItem& item, const LocalTypeNames& locals,
                      const PrefixWalk& walk) {
  const DataType* bound = &item.typedef_type;
  for (auto it = locals.rbegin(); it != locals.rend(); ++it) {
    if (NamesLocal(*bound, *it)) bound = it->bound;
  }
  ReportTypeOutsideRestriction({item.name, item.forward_type_kind}, *bound,
                               item.loc, walk.restriction, walk.diag);
}

void DeclareTypeName(const ModuleItem& item, bool is_param,
                     LocalTypeNames& locals, const PrefixWalk& walk) {
  JudgePrefix(item.typedef_type.scope_name, item.loc, locals, walk, true);
  JudgeTypeRef(item.typedef_type, item.loc, locals, walk);
  if (is_param) JudgeRestriction(item, locals, walk);
  locals.push_back({item.name, &item.typedef_type, is_param});
}

bool DeclaresTypeParam(const ModuleItem& item) {
  return item.kind == ModuleItemKind::kParamDecl &&
         item.data_type.kind == DataTypeKind::kVoid &&
         item.typedef_type.kind != DataTypeKind::kImplicit;
}

void WalkStmt(Stmt* s, LocalTypeNames& locals, const PrefixWalk& walk) {
  if (s == nullptr) return;
  const ModuleItem* item = s->decl_item;
  if (s->kind == StmtKind::kBlockItemDecl && item != nullptr &&
      item->kind == ModuleItemKind::kTypedef) {
    DeclareTypeName(*item, false, locals, walk);
  } else if (s->kind == StmtKind::kVarDecl && s->var_is_param &&
             item != nullptr && DeclaresTypeParam(*item)) {
    DeclareTypeName(*item, true, locals, walk);
  } else if (s->kind == StmtKind::kVarDecl) {
    JudgeTypeRef(s->var_decl_type, s->range.start, locals, walk);
  }
  LocalTypeNames inner = locals;
  ForEachChildStmt(s, [&](Stmt* sub) { WalkStmt(sub, inner, walk); });
}

void WalkProcedure(const ModuleItem& item, const LocalTypeNames& locals,
                   const PrefixWalk& walk) {
  LocalTypeNames inner = locals;
  WalkStmt(item.body, inner, walk);
  for (Stmt* s : item.func_body_stmts) WalkStmt(s, inner, walk);
}

bool DeclaresChecker(const ModuleItem& item) {
  return item.kind == ModuleItemKind::kNestedModuleDecl &&
         item.nested_module_decl != nullptr &&
         item.nested_module_decl->decl_kind == ModuleDeclKind::kChecker;
}

void WalkScopeItems(const std::vector<ModuleItem*>& items,
                    const PrefixWalk& walk) {
  LocalTypeNames locals;
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kTypedef) {
      DeclareTypeName(*item, false, locals, walk);
    } else if (DeclaresTypeParam(*item)) {
      DeclareTypeName(*item, true, locals, walk);
    } else if (item->kind == ModuleItemKind::kVarDecl) {
      JudgeTypeRef(item->data_type, item->loc, locals, walk);
    } else if (item->kind == ModuleItemKind::kFunctionDecl ||
               item->kind == ModuleItemKind::kTaskDecl) {
      WalkProcedure(*item, locals, walk);
    } else if (DeclaresChecker(*item)) {
      WalkScopeItems(item->nested_module_decl->items, walk);
    }
  }
}

}  // namespace

void ReportItemTypeParamErrors(const ModuleItem& item,
                               const TypeParamPrefixScope& scope,
                               const TypeParamRestrictionScope& restriction,
                               DiagEngine& diag) {
  if (DeclaresChecker(item)) {
    WalkScopeItems(item.nested_module_decl->items,
                   {&scope, restriction, diag, true});
    return;
  }
  WalkProcedure(item, {}, {&scope, restriction, diag});
}

void ReportUnitScopeTypeParamErrors(const TypeParamRestrictionScope& scope,
                                    DiagEngine& diag) {
  const PrefixWalk kWalk{nullptr, scope, diag};
  for (const PackageDecl* pkg : scope.unit->packages)
    WalkScopeItems(pkg->items, kWalk);
  WalkScopeItems(scope.unit->cu_items, kWalk);
  for (const ClassDecl* cls : AllClassDecls(scope.unit)) {
    for (const ClassMember* m : cls->members) {
      if (m->method != nullptr) WalkProcedure(*m->method, {}, kWalk);
    }
  }
}

void ReportTypeRefPrefixNotAClass(const Expr* ref, SourceLoc loc,
                                  const TypeParamPrefixScope& scope,
                                  DiagEngine& diag) {
  if (ref->kind != ExprKind::kMemberAccess || !ref->is_scope_resolution ||
      ref->lhs == nullptr || ref->lhs->kind != ExprKind::kIdentifier)
    return;
  ReportTypeParamPrefixNotAClass(ref->lhs->text, loc, scope, diag);
}

const DataType* TypeRefThroughBoundPrefix(std::string_view prefix,
                                          std::string_view name,
                                          const TypedefMap& typedefs) {
  DataType written;
  written.kind = DataTypeKind::kNamed;
  written.scope_name = prefix;
  written.type_name = name;
  if (!ThroughBoundPrefix(written, typedefs).has_value()) return nullptr;
  return FindNamedType(written, typedefs);
}

static const DataType* BoundActual(const ClassDecl& cls, size_t i,
                                   std::string_view name,
                                   const DataType& written) {
  for (const DataType& actual : written.type_params) {
    if (actual.param_arg_name == name) return &actual;
  }
  if (i < written.type_params.size() &&
      written.type_params[i].param_arg_name.empty())
    return &written.type_params[i];
  if (i < cls.param_types.size()) return &cls.param_types[i];
  return nullptr;
}

static bool BodySelectsThrough(const ClassDecl& cls, std::string_view name) {
  return std::ranges::any_of(cls.members, [&](const ClassMember* m) {
    return m->kind == ClassMemberKind::kTypedef && m->typedef_item != nullptr &&
           m->typedef_item->typedef_type.kind == DataTypeKind::kNamed &&
           m->typedef_item->typedef_type.scope_name == name &&
           m->typedef_item->typedef_type.outer_scope_names.empty();
  });
}

static void ReportSpecializationPrefixNotAClass(const DataType& written,
                                                SourceLoc loc,
                                                const CompilationUnit* unit,
                                                DiagEngine& diag) {
  if (written.kind != DataTypeKind::kNamed || !written.scope_name.empty())
    return;
  const ClassDecl* cls = FindClassDecl(written.type_name, unit);
  if (cls == nullptr) return;
  for (size_t i = 0; i < cls->params.size(); ++i) {
    std::string_view name = cls->params[i].first;
    if (!cls->type_param_names.contains(name) ||
        !BodySelectsThrough(*cls, name))
      continue;
    const DataType* actual = BoundActual(*cls, i, name, written);
    if (actual == nullptr || actual->kind == DataTypeKind::kNamed ||
        actual->kind == DataTypeKind::kImplicit)
      continue;
    diag.ErrorOnce(loc,
                   std::format("type parameter '{}' used as a class scope "
                               "resolution prefix does not resolve to a class",
                               name),
                   Subclause("6.20.3"));
  }
}

void ReportSpecializationBindingErrors(const DataType& written, SourceLoc loc,
                                       const TypeParamRestrictionScope& scope,
                                       DiagEngine& diag) {
  ReportSpecializationPrefixNotAClass(written, loc, scope.unit, diag);
  ReportSpecializationOutsideRestrictions(written, loc, scope, diag);
}

void ReportUnitSpecializations(const TypeParamRestrictionScope& scope,
                               DiagEngine& diag) {
  for (const ModuleItem* item : scope.unit->cu_items) {
    if (item->kind == ModuleItemKind::kTypedef) {
      ReportSpecializationBindingErrors(item->typedef_type, item->loc, scope,
                                        diag);
    } else if (item->kind == ModuleItemKind::kVarDecl) {
      ReportSpecializationBindingErrors(item->data_type, item->loc, scope,
                                        diag);
    }
  }
  for (const ClassDecl* cls : scope.unit->classes) {
    for (const ClassMember* m : cls->members) {
      if (m->kind == ClassMemberKind::kProperty) {
        ReportSpecializationBindingErrors(m->data_type, m->loc, scope, diag);
      } else if (m->kind == ClassMemberKind::kTypedef &&
                 m->typedef_item != nullptr) {
        ReportSpecializationBindingErrors(m->typedef_item->typedef_type, m->loc,
                                          scope, diag);
      }
    }
  }
}

}  // namespace delta
