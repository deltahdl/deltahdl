#include "elaborator/type_ref_walks.h"

#include <algorithm>
#include <cstddef>
#include <functional>
#include <span>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "elaborator/assoc_index_type.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_ref_dynamic_element.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

void ResolveLocalTypeRef(DataType& dt, std::vector<Expr*>& unpacked_dims,
                         SourceLoc loc,
                         const std::vector<ProceduralLocal>& locals,
                         const TypeRefResolver& resolve_outer) {
  const Expr* ref = dt.type_ref_expr;
  if (ref == nullptr) return;
  auto local = std::find_if(
      locals.rbegin(), locals.rend(), [&](const ProceduralLocal& l) {
        return ref->kind == ExprKind::kIdentifier && l.name == ref->text;
      });
  const std::vector<Expr*> kTaken = local == locals.rend()
                                        ? resolve_outer(dt, loc, locals)
                                        : *local->unpacked_dims;
  if (local != locals.rend()) dt = *local->type;
  unpacked_dims.insert(unpacked_dims.end(), kTaken.begin(), kTaken.end());
}

void DeclareForLoopLocals(Stmt* s, std::vector<ProceduralLocal>& locals,
                          const TypeRefResolver& resolve_outer) {
  if (s->kind != StmtKind::kFor) return;
  static const std::vector<Expr*> kNoUnpackedDims;
  const size_t kCount = std::min(s->for_inits.size(), s->for_init_types.size());
  for (size_t k = 0; k < kCount; ++k) {
    DataType& type = s->for_init_types[k];
    std::vector<Expr*> taken_dims;
    ResolveLocalTypeRef(type, taken_dims, s->range.start, locals,
                        resolve_outer);
    if (type.kind == DataTypeKind::kImplicit) continue;
    locals.push_back(
        {ExprIdent(s->for_inits[k]->lhs), &type, &kNoUnpackedDims});
  }
}

void ResolveLocalIndexTypeRefs(std::vector<Expr*>& dims, SourceLoc loc,
                               const std::vector<ProceduralLocal>& locals,
                               const TypeRefResolver& resolve_outer,
                               Arena& arena) {
  ResolveTypeRefIndexDims(
      dims,
      [&](DataType& type) {
        std::vector<Expr*> taken_dims;
        ResolveLocalTypeRef(type, taken_dims, loc, locals, resolve_outer);
      },
      arena);
}

void ResolveFormalTypeRefs(ModuleItem* item,
                           std::vector<ProceduralLocal>& locals,
                           const TypeRefResolver& resolve_outer, Arena& arena) {
  for (auto& arg : item->func_args) {
    ResolveLocalTypeRef(arg.data_type, arg.unpacked_dims, item->loc, locals,
                        resolve_outer);
    ResolveLocalIndexTypeRefs(arg.unpacked_dims, item->loc, locals,
                              resolve_outer, arena);
    locals.push_back({arg.name, &arg.data_type, &arg.unpacked_dims});
  }
}

void ResolveTypeRefsInStmt(Stmt* s, std::vector<ProceduralLocal>& locals,
                           const TypeRefResolver& resolve_outer, Arena& arena,
                           const ProceduralStmtVisitor& visit) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kBlockItemDecl &&
      s->decl_item->kind == ModuleItemKind::kLetDecl) {
    std::vector<ProceduralLocal> in_let = locals;
    ResolveFormalTypeRefs(s->decl_item, in_let, resolve_outer, arena);
    return;
  }
  if (s->kind != StmtKind::kVarDecl) {
    const size_t kOuter = locals.size();
    DeclareForLoopLocals(s, locals, resolve_outer);
    if (visit) visit(s, locals);
    ForEachChildStmt(s, [&](Stmt* const& sub) {
      ResolveTypeRefsInStmt(sub, locals, resolve_outer, arena, visit);
    });
    locals.resize(kOuter);
    return;
  }
  ResolveLocalTypeRef(s->var_decl_type, s->var_unpacked_dims, s->range.start,
                      locals, resolve_outer);
  ResolveLocalIndexTypeRefs(s->var_unpacked_dims, s->range.start, locals,
                            resolve_outer, arena);
  if (visit) visit(s, locals);
  locals.push_back({s->var_name, &s->var_decl_type, &s->var_unpacked_dims});
}

const Expr* PropertyName(const Expr& ref) {
  const Expr* name = &ref;
  if (ref.kind == ExprKind::kMemberAccess && !ref.is_scope_resolution &&
      ref.lhs != nullptr && ref.lhs->kind == ExprKind::kIdentifier &&
      ref.lhs->text == "this") {
    name = ref.rhs;
  }
  if (name == nullptr || name->kind != ExprKind::kIdentifier) return nullptr;
  return name;
}

const ClassMember* PropertyNamed(const ClassDecl& cls, const Expr& ref,
                                 const CompilationUnit* unit) {
  const Expr* name = PropertyName(ref);
  if (name == nullptr) return nullptr;
  OwnedMember owned;
  if (unit != nullptr) {
    owned = FindMemberAndOwner(&cls, name->text, unit);
  } else {
    auto own = std::ranges::find_if(cls.members, [&](const ClassMember* m) {
      return m->name == name->text;
    });
    if (own != cls.members.end()) owned = {*own, &cls};
  }
  if (owned.member == nullptr ||
      owned.member->kind != ClassMemberKind::kProperty) {
    return nullptr;
  }
  if (owned.owner != &cls && !owned.owner->params.empty()) return nullptr;
  return owned.member;
}

std::vector<ProceduralLocal> PropertiesInScope(const ClassDecl& cls,
                                               const CompilationUnit& unit) {
  std::vector<const ClassDecl*> chain = {&cls};
  while (!chain.back()->base_class.empty()) {
    const ClassDecl* base = FindBaseClass(chain.back(), &unit);
    if (base == nullptr || !base->params.empty()) break;
    chain.push_back(base);
  }
  std::vector<ProceduralLocal> properties;
  for (auto c = chain.rbegin(); c != chain.rend(); ++c) {
    for (const ClassMember* m : (*c)->members) {
      if (m->kind == ClassMemberKind::kProperty)
        properties.push_back({m->name, &m->data_type, &m->unpacked_dims});
    }
  }
  return properties;
}

std::vector<ProceduralLocal> SelfHandles(const ClassDecl& cls, Arena& arena) {
  static const std::vector<Expr*> kNoUnpackedDims;
  auto* self = arena.Create<DataType>();
  self->kind = DataTypeKind::kNamed;
  self->type_name = cls.name;
  std::vector<ProceduralLocal> handles = {{"this", self, &kNoUnpackedDims}};
  if (cls.base_class.empty()) return handles;
  auto* base = arena.Create<DataType>();
  base->kind = DataTypeKind::kNamed;
  base->type_name = cls.base_class;
  base->scope_name = cls.base_class_scope;
  base->type_params = cls.base_class_type_params;
  handles.push_back({"super", base, &kNoUnpackedDims});
  return handles;
}

std::vector<ProceduralLocal> NamesInScope(
    std::span<const ProceduralLocal> outer,
    std::span<const ProceduralLocal> inner) {
  std::vector<ProceduralLocal> all(outer.begin(), outer.end());
  all.insert(all.end(), inner.begin(), inner.end());
  return all;
}

void ResolveItemIndexTypeRefs(ModuleItem& item, const TypeRefResolver& resolve,
                              Arena& arena) {
  ResolveTypeRefIndexDims(
      item.unpacked_dims, [&](DataType& type) { resolve(type, item.loc, {}); },
      arena);
}

static void ResolveTypedefTypeRef(ModuleItem& item,
                                  const TypeRefResolver& resolve,
                                  Arena& arena) {
  const std::vector<Expr*> kTaken = resolve(item.typedef_type, item.loc, {});
  item.unpacked_dims.insert(item.unpacked_dims.end(), kTaken.begin(),
                            kTaken.end());
  ResolveItemIndexTypeRefs(item, resolve, arena);
}

void ResolveScopeItemTypeRefs(const std::vector<ModuleItem*>& items,
                              const TypeRefResolver& resolve,
                              const CompilationUnit* unit, Arena& arena,
                              const ProceduralStmtVisitor& visit) {
  for (ModuleItem* item : items) {
    switch (item->kind) {
      case ModuleItemKind::kTypedef:
        ResolveTypedefTypeRef(*item, resolve, arena);
        break;
      case ModuleItemKind::kNettypeDecl:
        resolve(item->typedef_type, item->loc, {});
        break;
      case ModuleItemKind::kVarDecl:
        ResolveItemIndexTypeRefs(*item, resolve, arena);
        break;
      case ModuleItemKind::kFunctionDecl:
      case ModuleItemKind::kTaskDecl:
      case ModuleItemKind::kLetDecl:
        ResolveProceduralTypeRefs(item, resolve, arena, visit);
        break;
      case ModuleItemKind::kClassDecl:
        ResolveClassTypeRefs(*item->class_decl, resolve, unit, arena, visit);
        break;
      default:
        break;
    }
  }
}

void ForEachItemTypeRef(
    const std::vector<ModuleItem*>& items,
    const std::function<void(const Expr*, SourceLoc)>& on_ref) {
  for (const ModuleItem* item : items) {
    if ((item->kind == ModuleItemKind::kVarDecl ||
         item->kind == ModuleItemKind::kNetDecl) &&
        item->data_type.type_ref_expr != nullptr) {
      on_ref(item->data_type.type_ref_expr, item->loc);
    }
    ForEachItemExprTypeRef(item, on_ref);
  }
}

}  // namespace

void AdoptReferencedType(DataType& dt, const DataType& type) {
  dt.kind = type.kind;
  dt.is_signed = type.is_signed;
  dt.type_name = type.type_name;
  dt.scope_name = type.scope_name;
  dt.outer_scope_names = type.outer_scope_names;
  dt.type_params = type.type_params;
  dt.packed_dim_left = type.packed_dim_left;
  dt.packed_dim_right = type.packed_dim_right;
  dt.extra_packed_dims = type.extra_packed_dims;
  dt.type_ref_expr = nullptr;
}

void ResolveProceduralTypeRefs(ModuleItem* item,
                               const TypeRefResolver& resolve_outer,
                               Arena& arena,
                               const ProceduralStmtVisitor& visit) {
  std::vector<ProceduralLocal> locals;
  locals.reserve(item->func_args.size());
  ResolveFormalTypeRefs(item, locals, resolve_outer, arena);
  ResolveTypeRefsInStmt(item->body, locals, resolve_outer, arena, visit);
  for (auto* s : item->func_body_stmts) {
    ResolveTypeRefsInStmt(s, locals, resolve_outer, arena, visit);
  }
}

void ResolveClassTypeRefs(ClassDecl& cls, const TypeRefResolver& resolve_outer,
                          const CompilationUnit* unit, Arena& arena,
                          const ProceduralStmtVisitor& visit) {
  const std::vector<ProceduralLocal> kProperties =
      NamesInScope(SelfHandles(cls, arena), PropertiesInScope(cls, *unit));
  const TypeRefResolver kInClass =
      [&](DataType& dt, SourceLoc loc,
          std::span<const ProceduralLocal> locals) -> std::vector<Expr*> {
    const Expr* ref = dt.type_ref_expr;
    if (ref == nullptr) return {};
    if (const ClassMember* property = PropertyNamed(cls, *ref, unit)) {
      AdoptReferencedType(dt, property->data_type);
      return property->unpacked_dims;
    }
    return resolve_outer(dt, loc, NamesInScope(kProperties, locals));
  };
  ProceduralStmtVisitor in_class;
  if (visit) {
    in_class = [&](Stmt* s, std::span<const ProceduralLocal> locals) {
      visit(s, NamesInScope(kProperties, locals));
    };
  }
  for (ClassMember* m : cls.members) {
    switch (m->kind) {
      case ClassMemberKind::kProperty:
        ResolveLocalTypeRef(m->data_type, m->unpacked_dims, m->loc, {},
                            kInClass);
        ResolveTypeRefIndexDims(
            m->unpacked_dims,
            [&](DataType& type) { kInClass(type, m->loc, {}); }, arena);
        break;
      case ClassMemberKind::kMethod:
        ResolveProceduralTypeRefs(m->method, kInClass, arena, in_class);
        break;
      case ClassMemberKind::kTypedef:
        ResolveItemIndexTypeRefs(*m->typedef_item, kInClass, arena);
        break;
      case ClassMemberKind::kClassDecl:
        ResolveClassTypeRefs(*m->nested_class, kInClass, unit, arena, in_class);
        break;
      default:
        break;
    }
  }
}

static void ForEachUnitScope(
    CompilationUnit* unit,
    const std::function<void(const PackageDecl*,
                             const std::vector<ModuleItem*>&)>& on_items,
    const std::function<void(ClassDecl&)>& on_class) {
  for (const PackageDecl* pkg : unit->packages) on_items(pkg, pkg->items);
  on_items(nullptr, unit->cu_items);
  for (ClassDecl* cls : unit->classes) on_class(*cls);
}

void ResolveUnitScopeTypeRefs(CompilationUnit* unit, Arena& arena,
                              std::vector<UnitScopeTypeRef>& written) {
  const PackageDecl* package = nullptr;
  const std::vector<ModuleItem*>* items = nullptr;
  auto record = [&](const Expr* operand, SourceLoc loc,
                    std::span<const ProceduralLocal> locals) {
    written.push_back({operand, loc, package, {locals.begin(), locals.end()}});
  };
  const TypeRefResolver kInScope =
      [&](DataType& dt, SourceLoc loc,
          std::span<const ProceduralLocal> locals) -> std::vector<Expr*> {
    if (dt.type_ref_expr != nullptr) record(dt.type_ref_expr, loc, locals);
    return ResolveScopeTypeRef(dt, *items, arena);
  };
  const ProceduralStmtVisitor kVisit =
      [&](Stmt* s, std::span<const ProceduralLocal> locals) {
        ForEachTypeRefOfStmt(s, [&](const Expr* ref) {
          record(ref->lhs, ref->range.start, locals);
        });
      };
  ForEachUnitScope(
      unit,
      [&](const PackageDecl* pkg, const std::vector<ModuleItem*>& scope_items) {
        package = pkg;
        items = &scope_items;
        ForEachItemTypeRef(scope_items,
                           [&](const Expr* operand, SourceLoc loc) {
                             record(operand, loc, {});
                           });
        ResolveScopeItemTypeRefs(scope_items, kInScope, unit, arena, kVisit);
      },
      [&](ClassDecl& cls) {
        package = nullptr;
        ResolveClassTypeRefs(cls, kInScope, unit, arena, kVisit);
      });
}

void ResolveUnitScopeProcedureTypeRefs(
    CompilationUnit* unit, Arena& arena,
    const std::function<void(const PackageDecl*)>& enter,
    const TypeRefResolver& resolve, const ProceduralStmtVisitor& visit) {
  ForEachUnitScope(
      unit,
      [&](const PackageDecl* pkg, const std::vector<ModuleItem*>& items) {
        enter(pkg);
        for (ModuleItem* item : items) {
          if (item->kind == ModuleItemKind::kFunctionDecl ||
              item->kind == ModuleItemKind::kTaskDecl) {
            ResolveProceduralTypeRefs(item, resolve, arena, visit);
          } else if (item->kind == ModuleItemKind::kClassDecl &&
                     item->class_decl->params.empty()) {
            ResolveClassTypeRefs(*item->class_decl, resolve, unit, arena,
                                 visit);
          }
        }
      },
      [&](ClassDecl& cls) {
        enter(nullptr);
        if (cls.params.empty())
          ResolveClassTypeRefs(cls, resolve, unit, arena, visit);
      });
}

}  // namespace delta
