#include "elaborator/type_ref_walks.h"

#include <algorithm>
#include <cstddef>
#include <optional>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "elaborator/assoc_index_type.h"
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

// A name a procedure declares, with the type and unpacked dimensions it was
// declared with.
struct ProceduralLocal {
  std::string_view name;
  const DataType* type;
  const std::vector<Expr*>* unpacked_dims;
};

// §6.23 with A.2.8: `var type(a) v;` among a block's items declares v with the
// self-determined type of `a`, taken with the names in scope at the
// declaration. A name the procedure declared earlier, in this block or one
// enclosing it, or as a formal of the subroutine, hides the scope's around the
// procedure, and v takes that declaration's type and unpacked dimensions; any
// other reference is left to `resolve_outer`. `locals` holds the procedure's
// names in declaration order.
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
  if (local == locals.rend()) {
    resolve_outer(dt, loc);
    return;
  }
  dt = *local->type;
  if (unpacked_dims.empty()) unpacked_dims = *local->unpacked_dims;
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

// Resolves the block type references of `s` and the statements it holds, with
// `locals` the names in scope ahead of it; a block's own names, and a for
// loop's, are dropped when the walk leaves it.
void ResolveTypeRefsInStmt(Stmt* s, std::vector<ProceduralLocal>& locals,
                           const TypeRefResolver& resolve_outer, Arena& arena) {
  if (s == nullptr) return;
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

// The type of the property of `cls` the type reference `ref` names, nothing
// where its argument names no property of the class.
std::optional<DataType> PropertyTypeNamed(const ClassDecl& cls,
                                          const Expr& ref) {
  if (ref.kind != ExprKind::kIdentifier) return std::nullopt;
  auto named = std::ranges::find_if(cls.members, [&](const ClassMember* m) {
    return m->kind == ClassMemberKind::kProperty && m->name == ref.text;
  });
  if (named == cls.members.end()) return std::nullopt;
  return (*named)->data_type;
}

// The type references the declarations of `items`, a package's or the
// compilation unit's, write in their typedefs' and nettypes' types, their
// variables' associative indexes (A.2.5), their subroutines and their
// classes, with `resolve` resolving a name none of them declares more
// closely.
void ResolveScopeItemTypeRefs(const std::vector<ModuleItem*>& items,
                              const TypeRefResolver& resolve, Arena& arena) {
  for (ModuleItem* item : items) {
    switch (item->kind) {
      case ModuleItemKind::kTypedef:
      case ModuleItemKind::kNettypeDecl:
        resolve(item->typedef_type, item->loc);
        break;
      case ModuleItemKind::kVarDecl:
        ResolveTypeRefIndexDims(
            item->unpacked_dims,
            [&](DataType& type) { resolve(type, item->loc); }, arena);
        break;
      case ModuleItemKind::kFunctionDecl:
      case ModuleItemKind::kTaskDecl:
        ResolveProceduralTypeRefs(item, resolve, arena);
        break;
      case ModuleItemKind::kClassDecl:
        ResolveClassTypeRefs(*item->class_decl, resolve, arena);
        break;
      default:
        break;
    }
  }
}

}  // namespace

// The procedures an item holds, an initial, final or always block's body and a
// task's or function's, are walked with the subroutine's formals as the first
// names in scope. A formal's own type may be a type reference, to an earlier
// formal or to a name of the scope around the subroutine.
void ResolveProceduralTypeRefs(ModuleItem* item,
                               const TypeRefResolver& resolve_outer,
                               Arena& arena) {
  std::vector<ProceduralLocal> locals;
  locals.reserve(item->func_args.size());
  for (auto& arg : item->func_args) {
    ResolveLocalTypeRef(arg.data_type, arg.unpacked_dims, item->loc, locals,
                        resolve_outer);
    ResolveLocalIndexTypeRefs(arg.unpacked_dims, item->loc, locals,
                              resolve_outer, arena);
    locals.push_back({arg.name, &arg.data_type, &arg.unpacked_dims});
  }
  ResolveTypeRefsInStmt(item->body, locals, resolve_outer, arena);
  for (auto* s : item->func_body_stmts) {
    ResolveTypeRefsInStmt(s, locals, resolve_outer, arena);
  }
}

// A name `type(this)` writes, which §8.11 has stand for the class itself, is
// none of the class's properties and is left to `resolve_outer`, which leaves
// it as written for the method's evaluation to read.
void ResolveClassTypeRefs(ClassDecl& cls, const TypeRefResolver& resolve_outer,
                          Arena& arena) {
  const TypeRefResolver kInClass = [&](DataType& dt, SourceLoc loc) {
    const Expr* ref = dt.type_ref_expr;
    if (ref == nullptr) return;
    if (std::optional<DataType> type = PropertyTypeNamed(cls, *ref)) {
      AdoptReferencedType(dt, *type);
      return;
    }
    resolve_outer(dt, loc);
  };
  for (ClassMember* m : cls.members) {
    switch (m->kind) {
      case ClassMemberKind::kProperty:
        kInClass(m->data_type, m->loc);
        ResolveTypeRefIndexDims(
            m->unpacked_dims, [&](DataType& type) { kInClass(type, m->loc); },
            arena);
        break;
      case ClassMemberKind::kMethod:
        ResolveProceduralTypeRefs(m->method, kInClass, arena);
        break;
      case ClassMemberKind::kClassDecl:
        ResolveClassTypeRefs(*m->nested_class, kInClass, arena);
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
        [&](DataType& dt, SourceLoc) {
          ResolveScopeTypeRef(dt, pkg->items, arena);
        },
        arena);
  }
  const TypeRefResolver kInUnit = [&](DataType& dt, SourceLoc) {
    ResolveScopeTypeRef(dt, unit->cu_items, arena);
  };
  ResolveScopeItemTypeRefs(unit->cu_items, kInUnit, arena);
  for (ClassDecl* cls : unit->classes) {
    ResolveClassTypeRefs(*cls, kInUnit, arena);
  }
}

}  // namespace delta
