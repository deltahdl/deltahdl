#include "elaborator/type_ref_walks.h"

#include <algorithm>
#include <cstddef>
#include <span>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "elaborator/assoc_index_type.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
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
// only within the let.
void ResolveTypeRefsInStmt(Stmt* s, std::vector<ProceduralLocal>& locals,
                           const TypeRefResolver& resolve_outer, Arena& arena) {
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
    ForEachChildStmt(s, [&](Stmt* const& sub) {
      ResolveTypeRefsInStmt(sub, locals, resolve_outer, arena);
    });
    locals.resize(kOuter);
    return;
  }
  ResolveLocalTypeRef(s->var_decl_type, s->var_unpacked_dims, s->range.start,
                      locals, resolve_outer);
  ResolveLocalIndexTypeRefs(s->var_unpacked_dims, s->range.start, locals,
                            resolve_outer, arena);
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
// name none of them declares more closely.
void ResolveScopeItemTypeRefs(const std::vector<ModuleItem*>& items,
                              const TypeRefResolver& resolve,
                              const CompilationUnit* unit, Arena& arena) {
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
        ResolveProceduralTypeRefs(item, resolve, arena);
        break;
      case ModuleItemKind::kClassDecl:
        ResolveClassTypeRefs(*item->class_decl, resolve, unit, arena);
        break;
      default:
        break;
    }
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
                               Arena& arena) {
  std::vector<ProceduralLocal> locals;
  locals.reserve(item->func_args.size());
  ResolveFormalTypeRefs(item, locals, resolve_outer, arena);
  ResolveTypeRefsInStmt(item->body, locals, resolve_outer, arena);
  for (auto* s : item->func_body_stmts) {
    ResolveTypeRefsInStmt(s, locals, resolve_outer, arena);
  }
}

// A name `type(this)` writes, which §8.11 has stand for the class itself, is
// none of the class's properties and is left to `resolve_outer`, which leaves
// it as written for the method's evaluation to read.
void ResolveClassTypeRefs(ClassDecl& cls, const TypeRefResolver& resolve_outer,
                          const CompilationUnit* unit, Arena& arena) {
  const TypeRefResolver kInClass =
      [&](DataType& dt, SourceLoc loc,
          std::span<const ProceduralLocal> locals) -> std::vector<Expr*> {
    const Expr* ref = dt.type_ref_expr;
    if (ref == nullptr) return {};
    if (const ClassMember* property = PropertyNamed(cls, *ref, unit)) {
      AdoptReferencedType(dt, property->data_type);
      return property->unpacked_dims;
    }
    return resolve_outer(dt, loc, locals);
  };
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
        ResolveProceduralTypeRefs(m->method, kInClass, arena);
        break;
      case ClassMemberKind::kTypedef:
        ResolveItemIndexTypeRefs(*m->typedef_item, kInClass, arena);
        break;
      case ClassMemberKind::kClassDecl:
        ResolveClassTypeRefs(*m->nested_class, kInClass, unit, arena);
        break;
      default:
        break;
    }
  }
}

void ResolveUnitScopeTypeRefs(CompilationUnit* unit, Arena& arena) {
  for (const PackageDecl* pkg : unit->packages) {
    ResolveScopeItemTypeRefs(
        pkg->items,
        [&](DataType& dt, SourceLoc,
            std::span<const ProceduralLocal>) -> std::vector<Expr*> {
          ResolveScopeTypeRef(dt, pkg->items, arena);
          return {};
        },
        unit, arena);
  }
  const TypeRefResolver kInUnit =
      [&](DataType& dt, SourceLoc,
          std::span<const ProceduralLocal>) -> std::vector<Expr*> {
    ResolveScopeTypeRef(dt, unit->cu_items, arena);
    return {};
  };
  ResolveScopeItemTypeRefs(unit->cu_items, kInUnit, unit, arena);
  for (ClassDecl* cls : unit->classes) {
    ResolveClassTypeRefs(*cls, kInUnit, unit, arena);
  }
}

}  // namespace delta
