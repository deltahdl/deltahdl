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

// §6.23 with A.2.8: `var type(a) v;` among a block's items declares v with the
// self-determined type of `a`, taken with the names in scope at the
// declaration. A name the procedure declared earlier, in this block or one
// enclosing it, or as a formal of the subroutine, hides the scope's around the
// procedure, and v takes that declaration's type and unpacked dimensions; any
// other reference is left to `resolve_outer`. The dimensions taken stand
// inside those v writes, as an array typedef's do (§7.4.4). `locals` holds the
// procedure's names in declaration order.
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

// §6.23 with §12.7.1: the variables the header of `s`, where it is a for loop,
// declares, each of whose type may be a type reference, resolved as a block's
// declaration's is and then in scope for the loop's own statements. An
// initialization whose type is implicit assigns a variable declared elsewhere.
// A loop variable has no unpacked dimensions to take from what it names.
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

// A.2.5 with §6.23: the associative indexes among `dims`, the unpacked
// dimensions of a declaration a procedure writes at `loc`, written as a type
// reference to an expression, `[type(k)]`, given the type of `k` as a type
// reference the declaration's own type writes is: a name the procedure
// declared earlier takes that declaration's type, and any other is left to
// `resolve_outer`. A name's unpacked dimensions are no part of an index type
// and are not taken.
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

// The formals of `item`, a subroutine or a let, each resolved with `locals`,
// the names in scope ahead of the item, and the formals before it, which are
// added to `locals` in turn. A formal's own type may be a type reference, to
// an earlier formal or to a name of the scope around the item.
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

// Resolves the block type references of `s` and the statements it holds, with
// `locals` the names in scope ahead of it; a block's own names, and a for
// loop's, are dropped when the walk leaves it. §11.12 lets a block declare a
// let, whose formals see the block's names ahead of them and are in scope
// only within the let. `visit`, where given, is shown each statement but a
// let's declaration with the names in scope at it: a for loop's own names
// among them, and a declaration's own name not, since its initializer sees
// only the names declared ahead of it (§6.21).
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

// The name of a property the type reference `ref` writes in a method: bare,
// or selected of `this` (§8.11). Null for any other expression.
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

// §8.5 and §8.13: the property of `cls`, or of a class it extends, that the
// type reference `ref` names; null where its argument names none, and where a
// parameterized base class declares it, whose type the specialization `cls`
// extends gives. Without `unit` the class's own properties alone are read.
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

// §8.5 and §8.13: the properties of `cls` and of the classes it extends, as
// names in scope in its methods, those of the class furthest up the chain
// first, so that a property a class declares hides one it inherits. The chain
// stops at a parameterized base class, whose properties' types the
// specialization `cls` extends gives (PropertyNamed), and at a base class
// `unit` does not declare. The elaborator has broken every cycle of extends
// clauses before the walk, so the chain ends.
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

// §8.11 and §8.15: the handles a method of `cls` reads its own object
// through, `this` of the class's type and, where the class extends another,
// `super` of the type of the class it extends, as names in scope in its
// methods; their types are made in `arena`.
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

// The names `outer` holds followed by those `inner` holds, which hide them.
std::vector<ProceduralLocal> NamesInScope(
    std::span<const ProceduralLocal> outer,
    std::span<const ProceduralLocal> inner) {
  std::vector<ProceduralLocal> all(outer.begin(), outer.end());
  all.insert(all.end(), inner.begin(), inner.end());
  return all;
}

// A.2.5 with §6.23: the associative indexes the declaration `item`, a
// variable or a typedef, writes as type references, `[type(k)]`, given the
// types `resolve` gives their arguments, made in `arena`.
void ResolveItemIndexTypeRefs(ModuleItem& item, const TypeRefResolver& resolve,
                              Arena& arena) {
  ResolveTypeRefIndexDims(
      item.unpacked_dims, [&](DataType& type) { resolve(type, item.loc, {}); },
      arena);
}

// The type references the declarations of `items`, a package's or the
// compilation unit's, write in their typedefs' and nettypes' types, their
// typedefs' and variables' associative indexes (A.2.5), their subroutines,
// their lets' formals (§11.12) and their classes, with `resolve` resolving a
// name none of them declares more closely. `visit` is shown each statement of
// their subroutines and methods as ResolveProceduralTypeRefs shows it.
void ResolveScopeItemTypeRefs(const std::vector<ModuleItem*>& items,
                              const TypeRefResolver& resolve,
                              const CompilationUnit* unit, Arena& arena,
                              const ProceduralStmtVisitor& visit) {
  for (ModuleItem* item : items) {
    switch (item->kind) {
      case ModuleItemKind::kTypedef:
        resolve(item->typedef_type, item->loc, {});
        ResolveItemIndexTypeRefs(*item, resolve, arena);
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

// §6.23: shows `on_ref` the operand of each type reference the declarations
// among `items` write outside any statement, with where it is written: a
// variable's or net's type and the expressions ForEachItemExprTypeRef names.
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

// The procedures an item holds, an initial, final or always block's body and a
// task's or function's, are walked with the subroutine's formals as the first
// names in scope.
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

// A name `type(this)` writes, which §8.11 has stand for the class itself, is
// none of the class's properties and is left to `resolve_outer`, which leaves
// it as written for the method's evaluation to read.
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

// The package and compilation-unit scopes of `unit`: `on_items` is shown each
// package's items with the package, then the unit's own with none; `on_class`
// each class declared at the unit's top, outside every package.
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
    ResolveScopeTypeRef(dt, *items, arena);
    return {};
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
