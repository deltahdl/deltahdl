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
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

// §6.20.3: the check that a type parameter prefixing the class scope
// resolution operator resolves to a class, made with the type each instance
// binds the parameter to.

namespace delta {

// Whether `type` is a class or a name the scope does not resolve, following a
// typedef or type parameter naming another by a bare name to the type it ends
// at. Only a type that ends at something other than a name is known to be no
// class.
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

// A type name a scope declares among its own items, in the order written: a
// type parameter or a typedef, with the type it stands for. A later one of
// the same name hides an earlier.
struct LocalTypeName {
  std::string_view name;
  const DataType* bound;
  bool is_param;
};

using LocalTypeNames = std::vector<LocalTypeName>;

// What a walk over a scope's items reports against: the instance's scope for
// a prefix the items do not declare themselves, none in a package or the
// compilation unit, whose type parameters are all their own. A type operator
// naming the instance's parameter is judged against it only where
// `outer_type_refs`: in a checker the instance declares, which is elaborated
// as an instance of its own that does not see the parameter.
struct PrefixWalk {
  const TypeParamPrefixScope* outer;
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

// Whether the type `local` stands for, followed through the scope's own names
// bound by a bare name, ends at a type that is no class. A name the scope
// does not declare may be a class, and is not known to be none.
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

// Judges `prefix`, written at `loc`: by the scope's own declaration of the
// name where it has one, and otherwise, where `outer_too`, by the instance's.
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

// The prefix of a type operator's argument written as one name scoped by
// another, `type(T::inner)`; empty for any other argument.
std::string_view TypeRefPrefix(const DataType& type) {
  const Expr* ref = type.type_ref_expr;
  if (ref == nullptr || ref->kind != ExprKind::kMemberAccess ||
      !ref->is_scope_resolution || ref->lhs == nullptr ||
      ref->lhs->kind != ExprKind::kIdentifier)
    return {};
  return ref->lhs->text;
}

// The type operator `type` writes. An instance's own type parameter is judged
// where the reference is resolved (ReportTypeRefPrefixNotAClass), so outside a
// checker only the scope's own names are judged here.
void JudgeTypeRef(const DataType& type, SourceLoc loc,
                  const LocalTypeNames& locals, const PrefixWalk& walk) {
  JudgePrefix(TypeRefPrefix(type), loc, locals, walk, walk.outer_type_refs);
}

// A typedef or a type parameter `item` declares, judged and then entered among
// the scope's names, which the items after it see.
void DeclareTypeName(const ModuleItem& item, bool is_param,
                     LocalTypeNames& locals, const PrefixWalk& walk) {
  JudgePrefix(item.typedef_type.scope_name, item.loc, locals, walk,
              /*outer_too=*/true);
  JudgeTypeRef(item.typedef_type, item.loc, locals, walk);
  locals.push_back({item.name, &item.typedef_type, is_param});
}

bool DeclaresTypeParam(const ModuleItem& item) {
  return item.kind == ModuleItemKind::kParamDecl &&
         item.data_type.kind == DataTypeKind::kVoid &&
         item.typedef_type.kind != DataTypeKind::kImplicit;
}

// The statement `s` and those under it, a block's items declaring names its
// later statements and nested blocks see; a nested block's names end with it.
void WalkStmt(Stmt* s, LocalTypeNames& locals, const PrefixWalk& walk) {
  if (s == nullptr) return;
  const ModuleItem* item = s->decl_item;
  if (s->kind == StmtKind::kBlockItemDecl && item != nullptr &&
      item->kind == ModuleItemKind::kTypedef) {
    DeclareTypeName(*item, /*is_param=*/false, locals, walk);
  } else if (s->kind == StmtKind::kVarDecl && s->var_is_param &&
             item != nullptr && DeclaresTypeParam(*item)) {
    DeclareTypeName(*item, /*is_param=*/true, locals, walk);
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

// A package's, the compilation unit's or a checker's items, in order.
void WalkScopeItems(const std::vector<ModuleItem*>& items,
                    const PrefixWalk& walk) {
  LocalTypeNames locals;
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kTypedef) {
      DeclareTypeName(*item, /*is_param=*/false, locals, walk);
    } else if (DeclaresTypeParam(*item)) {
      DeclareTypeName(*item, /*is_param=*/true, locals, walk);
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

void ReportItemPrefixesNotAClass(const ModuleItem& item,
                                 const TypeParamPrefixScope& scope,
                                 DiagEngine& diag) {
  if (DeclaresChecker(item)) {
    WalkScopeItems(item.nested_module_decl->items,
                   {&scope, diag, /*outer_type_refs=*/true});
    return;
  }
  WalkProcedure(item, {}, {&scope, diag});
}

void ReportUnitScopePrefixesNotAClass(const CompilationUnit* unit,
                                      DiagEngine& diag) {
  for (const PackageDecl* pkg : unit->packages)
    WalkScopeItems(pkg->items, {nullptr, diag});
  WalkScopeItems(unit->cu_items, {nullptr, diag});
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

// The type `cls` binds its type parameter at index `i`, named `name`, to under
// the actuals `written` gives: the one named for it, else the one at its
// position, else the class's default. Null where none is given.
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

// Whether the body of `cls` selects a type through its type parameter
// `name`, in a typedef or a body `localparam type` (carried as a typedef).
static bool BodySelectsThrough(const ClassDecl& cls, std::string_view name) {
  return std::ranges::any_of(cls.members, [&](const ClassMember* m) {
    return m->kind == ClassMemberKind::kTypedef && m->typedef_item != nullptr &&
           m->typedef_item->typedef_type.kind == DataTypeKind::kNamed &&
           m->typedef_item->typedef_type.scope_name == name &&
           m->typedef_item->typedef_type.outer_scope_names.empty();
  });
}

void ReportSpecializationPrefixNotAClass(const DataType& written, SourceLoc loc,
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

void ReportUnitSpecializations(const CompilationUnit* unit, DiagEngine& diag) {
  for (const ModuleItem* item : unit->cu_items) {
    if (item->kind == ModuleItemKind::kTypedef) {
      ReportSpecializationPrefixNotAClass(item->typedef_type, item->loc, unit,
                                          diag);
    } else if (item->kind == ModuleItemKind::kVarDecl) {
      ReportSpecializationPrefixNotAClass(item->data_type, item->loc, unit,
                                          diag);
    }
  }
  for (const ClassDecl* cls : unit->classes) {
    for (const ClassMember* m : cls->members) {
      if (m->kind == ClassMemberKind::kProperty) {
        ReportSpecializationPrefixNotAClass(m->data_type, m->loc, unit, diag);
      } else if (m->kind == ClassMemberKind::kTypedef &&
                 m->typedef_item != nullptr) {
        ReportSpecializationPrefixNotAClass(m->typedef_item->typedef_type,
                                            m->loc, unit, diag);
      }
    }
  }
}

}  // namespace delta
