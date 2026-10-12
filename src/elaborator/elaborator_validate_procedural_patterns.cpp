#include <algorithm>
#include <cstddef>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/elaborator_validate_operations.h"
#include "elaborator/net_data_type.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

// Whether a block the walk is inside declares `name`, which hides the module's
// declaration of it for the rest of that block (§6.21, §23.9).
static bool IsBlockDeclared(
    const std::vector<std::pair<std::string_view, bool>>& decls,
    std::string_view name) {
  return std::ranges::any_of(
      decls, [name](const auto& decl) { return decl.first == name; });
}

// §5.10 with §5.11 and §10.9.1 holds a pattern to its array wherever it is
// written: assigned by a procedure to the module's array, `abarr = '{...}`, or
// initializing an array a block declares, a packed array (§7.4) among them.
// Only the module-level declaration's initializer was checked, so a flat
// pattern for an array of structures and a pattern of the wrong element count
// went through in both places.
void ElaboratorOperationRules::WalkStmtsForProceduralArrayPattern(
    const Stmt* s) {
  if (s == nullptr) return;
  const ArrayPatternCheck kCheck{typedefs_, aggregate_typedef_names_,
                                 var_types_, diag_};
  bool is_assign = s->kind == StmtKind::kBlockingAssign ||
                   s->kind == StmtKind::kNonblockingAssign;
  if (is_assign && s->lhs->kind == ExprKind::kIdentifier &&
      !IsBlockDeclared(block_decls_, s->lhs->text)) {
    auto it = pattern_target_arrays_.find(s->lhs->text);
    if (it != pattern_target_arrays_.end()) {
      kCheck.Check(s->rhs, it->second->data_type, it->second->unpacked_dims,
                   s->rhs->range.start);
    }
  }
  if (s->kind == StmtKind::kVarDecl && s->var_init != nullptr) {
    kCheck.Check(s->var_init, s->var_decl_type, s->var_unpacked_dims,
                 s->var_init->range.start);
  }
  size_t mark = block_decls_.size();
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForProceduralArrayPattern(sub); });
  block_decls_.resize(mark);
  if (s->kind == StmtKind::kVarDecl)
    block_decls_.emplace_back(s->var_name, !s->var_unpacked_dims.empty());
}

namespace {
// What a typed pattern's prefix is resolved in: the typedefs in scope, with the
// unpacked dimensions recorded for each array typedef, the module's variables
// and nets, and inside a process or a subroutine the declarations its
// statements see.
struct TypedPatternScope {
  const ArrayPatternCheck& check;
  const TypedefMap& typedefs;
  const std::unordered_map<std::string_view, std::vector<Expr*>>& td_array_dims;
  const std::unordered_map<std::string_view, const ModuleItem*>& module_vars;
  const BodyDeclScopes* body;
};

// The array type a typed pattern's prefix names: the type of its elements and
// its unpacked dimensions, outermost first, which ArrayPatternCheck follows
// into the packed dimensions of that element type.
struct PrefixArrayType {
  const DataType* elem;
  std::vector<Expr*> unpacked_dims;
};
}  // namespace

// §6.18: a typedef renaming another names the same type, so the unpacked
// dimensions an array typedef keeps (§7.4.4) are those recorded for the first
// name along the chain that has any, and that typedef's entry is the element
// type. Nothing for a name, or a chain, that no typedef in scope resolves, an
// integer atom type among them, which has no dimensions to count against.
static std::optional<PrefixArrayType> TypedefPrefixType(
    std::string_view name, const TypedPatternScope& scope) {
  DataType named;
  named.kind = DataTypeKind::kNamed;
  named.type_name = name;
  std::vector<std::string_view> chain;
  if (FollowTypedefs(named, scope.typedefs, chain) == nullptr)
    return std::nullopt;
  for (std::string_view link : chain) {
    auto dims = scope.td_array_dims.find(link);
    if (dims != scope.td_array_dims.end())
      return PrefixArrayType{&scope.typedefs.find(link)->second, dims->second};
  }
  return PrefixArrayType{&scope.typedefs.find(name)->second, {}};
}

// §6.23: `type(x)` stands for the type x is declared with, the declaration
// being the one visible where the reference is written -- a block's variable
// or a subroutine's formal, which hides the module's (§6.21), and otherwise
// the module's variable or net.
static std::optional<PrefixArrayType> TypeRefExprType(
    const Expr* ref, const TypedPatternScope& scope) {
  std::string_view name = ExprIdent(ref->lhs);
  if (scope.body != nullptr) {
    if (const BodyDeclScopes::Decl* decl = scope.body->Find(name))
      return PrefixArrayType{decl->type, *decl->unpacked_dims};
  }
  auto it = scope.module_vars.find(name);
  if (it == scope.module_vars.end()) return std::nullopt;
  return PrefixArrayType{&it->second->data_type, it->second->unpacked_dims};
}

// §26.3: the key RegisterScopedTypedef records a typedef behind a package's
// or a class's scope under, "p::T" for `p::T`. A bare name gives a key no
// typedef has.
static std::string ScopedTypedefKey(const Expr* scoped) {
  return std::string(ExprIdent(scoped->lhs)) +
         "::" + std::string(ExprIdent(scoped->rhs));
}

// §6.23 with §7.4.4: a data type `type(...)` encloses. A typedef's name
// written alone there is that typedef, unpacked dimensions included, as the
// name prefixing the pattern itself is. A type written out, a name under
// packed dimensions of its own, or a name behind a class's scope is the element
// type with no unpacked dimension.
static std::optional<PrefixArrayType> TypeValuePrefixType(
    const DataType* written, const TypedPatternScope& scope) {
  if (written->kind == DataTypeKind::kNamed &&
      written->packed_dim_left == nullptr && written->scope_name.empty())
    return TypedefPrefixType(written->type_name, scope);
  return PrefixArrayType{written, {}};
}

// §10.9: the type a typed pattern's prefix names. A name the parser knew as a
// type is the cast's own text. A prefix the parser read as an expression is a
// scope resolution, `p::T`, whose name before `::` is a package or a class
// and never a variable (§26.3). `type(...)` encloses a data type, or an
// expression, which a package's typedef `type(p::T)` is read as.
static std::optional<PrefixArrayType> PrefixType(
    const Expr* cast, const TypedPatternScope& scope) {
  const Expr* ref = cast->rhs;
  if (ref == nullptr) return TypedefPrefixType(cast->text, scope);
  if (ref->kind != ExprKind::kTypeRef)
    return TypedefPrefixType(ScopedTypedefKey(ref), scope);
  if (ref->type_value != nullptr)
    return TypeValuePrefixType(ref->type_value, scope);
  if (ref->lhs->is_scope_resolution)
    return TypedefPrefixType(ScopedTypedefKey(ref->lhs), scope);
  return TypeRefExprType(ref, scope);
}

// §10.9 with §10.9.1: a typed pattern, `T'{...}` or `type(x)'{...}`, parses as
// a cast wrapping the pattern and takes the type its prefix names in place of
// its context's, so its braces are counted against that type's dimensions
// wherever it is written -- an operand or a subroutine's return value as much
// as the right-hand side of an assignment.
static void CheckTypedArrayPatternsIn(const Expr* e,
                                      const TypedPatternScope& scope) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kCast &&
      e->lhs->kind == ExprKind::kAssignmentPattern) {
    if (auto type = PrefixType(e, scope)) {
      scope.check.Check(e->lhs, *type->elem, type->unpacked_dims,
                        e->range.start);
    }
  }
  ForEachExprChild(e, [&scope](const Expr* child) {
    CheckTypedArrayPatternsIn(child, scope);
  });
}

// The typed patterns a process's or a subroutine's statements write, each
// resolved among the declarations in view where it stands.
static void CheckProceduralTypedArrayPatterns(
    const std::vector<FunctionArg>& formals, const std::vector<Stmt*>& body,
    TypedPatternScope scope) {
  BodyDeclScopes decls(false);
  for (const auto& arg : formals) decls.DeclareFormal(arg);
  scope.body = &decls;
  for (const Stmt* s : body) {
    decls.Walk(s, [&scope](const Stmt* st) {
      ForEachChildExpr(
          st, [&scope](const Expr* e) { CheckTypedArrayPatternsIn(e, scope); });
    });
  }
}

// The typed patterns one module item writes: in its own expressions -- a
// declaration's initializer, both sides of a continuous assignment, an
// instance's port connections -- and in a process's or a subroutine's
// statements.
static void CheckItemTypedArrayPatterns(const ModuleItem* item,
                                        const TypedPatternScope& scope) {
  CheckTypedArrayPatternsIn(item->init_expr, scope);
  CheckTypedArrayPatternsIn(item->assign_lhs, scope);
  CheckTypedArrayPatternsIn(item->assign_rhs, scope);
  for (const auto& conn : item->inst_ports)
    CheckTypedArrayPatternsIn(conn.second, scope);
  if (IsProceduralItemKind(item->kind))
    CheckProceduralTypedArrayPatterns({}, {item->body}, scope);
  CheckProceduralTypedArrayPatterns(item->func_args, item->func_body_stmts,
                                    scope);
}

using StructTargetTypes = std::unordered_map<std::string_view, const DataType*>;

// The type a procedural assignment's target is declared with where the target
// names a whole variable that is no array: a name the body declares, which
// hides the module's, or a module variable of `module_types`.
static const DataType* WholeTargetType(const Expr* lhs,
                                       const BodyDeclScopes& scopes,
                                       const StructTargetTypes& module_types) {
  if (lhs->kind != ExprKind::kIdentifier) return nullptr;
  if (const BodyDeclScopes::Decl* decl = scopes.Find(lhs->text))
    return decl->unpacked_dims->empty() ? decl->type : nullptr;
  auto it = module_types.find(lhs->text);
  return it == module_types.end() ? nullptr : it->second;
}

// §10.9.2 (printed pages 263-264) holds a structure pattern to its structure
// wherever it is written -- a typed pattern to the type its prefix names, and
// an untyped one to the variable it is assigned to or initializes -- and not
// only where a module-level declaration is initialized.
static void CheckProceduralStructPatterns(
    const std::vector<FunctionArg>& formals, const std::vector<Stmt*>& body,
    const StructTargetTypes& module_types, const TypedefMap& typedefs,
    DiagEngine& diag) {
  BodyDeclScopes scopes(false);
  for (const auto& arg : formals) scopes.DeclareFormal(arg);
  for (const Stmt* s : body) {
    scopes.Walk(s, [&](const Stmt* st) {
      if (st->kind == StmtKind::kVarDecl && st->var_init != nullptr &&
          st->var_unpacked_dims.empty()) {
        CheckStructPatternFor(st->var_init, &st->var_decl_type,
                              {typedefs, st->var_init->range.start, diag});
      }
      if (st->kind != StmtKind::kBlockingAssign &&
          st->kind != StmtKind::kNonblockingAssign)
        return;
      CheckStructPatternFor(st->rhs,
                            WholeTargetType(st->lhs, scopes, module_types),
                            {typedefs, st->rhs->range.start, diag});
    });
  }
}

// The structure patterns one item writes: in a process's or a subroutine's
// statements, and on the right of a continuous assignment, whose target no
// block declaration hides.
static void CheckItemStructPatterns(const ModuleItem* item,
                                    const StructTargetTypes& targets,
                                    const TypedefMap& typedefs,
                                    DiagEngine& diag) {
  if (IsProceduralItemKind(item->kind))
    CheckProceduralStructPatterns({}, {item->body}, targets, typedefs, diag);
  CheckProceduralStructPatterns(item->func_args, item->func_body_stmts, targets,
                                typedefs, diag);
  if (item->kind != ModuleItemKind::kContAssign) return;
  const BodyDeclScopes kNoLocals(false);
  CheckStructPatternFor(item->assign_rhs,
                        WholeTargetType(item->assign_lhs, kNoLocals, targets),
                        {typedefs, item->assign_rhs->range.start, diag});
}

// §10.8 counts a continuous assignment and a net declaration assignment among
// the assignment-like contexts, so §10.9.1 holds the pattern each drives to the
// dimensions of its target: the variable or net its left-hand side names
// whole, or the net it declares.
void ElaboratorOperationRules::CheckContinuousArrayPattern(
    const ModuleItem* item) {
  const ArrayPatternCheck kCheck{typedefs_, aggregate_typedef_names_,
                                 var_types_, diag_};
  if (item->kind == ModuleItemKind::kNetDecl && item->init_expr != nullptr) {
    kCheck.Check(item->init_expr, item->data_type, item->unpacked_dims,
                 item->init_expr->range.start);
  }
  if (item->kind != ModuleItemKind::kContAssign ||
      item->assign_lhs->kind != ExprKind::kIdentifier)
    return;
  auto it = pattern_target_arrays_.find(item->assign_lhs->text);
  if (it == pattern_target_arrays_.end()) return;
  kCheck.Check(item->assign_rhs, it->second->data_type,
               it->second->unpacked_dims, item->assign_rhs->range.start);
}

// A subroutine's formals hide the module's declarations of their names in its
// body as a block's declarations do.
void ElaboratorOperationRules::ValidateProceduralArrayPatterns(
    const ModuleDecl* decl) {
  pattern_target_arrays_.clear();
  StructTargetTypes struct_targets;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kNetDecl)
      pattern_target_arrays_[item->name] = item;
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    pattern_target_arrays_[item->name] = item;
    if (item->unpacked_dims.empty())
      struct_targets[item->name] = &item->data_type;
  }
  const ArrayPatternCheck kCheck{typedefs_, aggregate_typedef_names_,
                                 var_types_, diag_};
  const TypedPatternScope kTypedScope{kCheck, typedefs_, td_array_dims_,
                                      pattern_target_arrays_, nullptr};
  for (const auto& param : decl->params)
    CheckTypedArrayPatternsIn(param.second, kTypedScope);
  for (const auto* item : decl->items) {
    CheckContinuousArrayPattern(item);
    CheckItemTypedArrayPatterns(item, kTypedScope);
    if (IsProceduralItemKind(item->kind))
      WalkStmtsForProceduralArrayPattern(item->body);
    CheckItemStructPatterns(item, struct_targets, typedefs_, diag_);
    for (const auto& arg : item->func_args)
      block_decls_.emplace_back(arg.name, !arg.unpacked_dims.empty());
    for (const auto* s : item->func_body_stmts)
      WalkStmtsForProceduralArrayPattern(s);
    block_decls_.clear();
  }
}

}  // namespace delta
