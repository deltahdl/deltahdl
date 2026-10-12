// §13.5.2: what may be passed to a ref argument, judged from the declaration
// of the name the actual is written with. The call walk in
// elaborator_validate_subroutine_args.cpp knows a name only as a net or not;
// this walk keeps, per procedure and per subroutine, what each name the actual
// can be is declared as: a module variable, a formal of the subroutine, or a
// local of its body, automatic or static.

#include <cstddef>
#include <format>
#include <string_view>
#include <unordered_map>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// What a name is declared as, where the walk can see the declaration.
struct RefDecl {
  const DataType* type = nullptr;
  bool unpacked = false;
  bool automatic = false;
  bool ref_without_static = false;
};

using RefScope = std::unordered_map<std::string_view, RefDecl>;
using FuncDecls = std::unordered_map<std::string_view, const ModuleItem*>;

// One ref formal and the actual a call binds it to.
struct RefBinding {
  const ModuleItem* func;
  const FunctionArg& formal;
  const Expr* actual;
  const Expr* root;
  const RefDecl& decl;
};

const Expr* RootIdentifier(const Expr* e) {
  while (e != nullptr && e->kind == ExprKind::kSelect) e = e->base;
  return e != nullptr && e->kind == ExprKind::kIdentifier ? e : nullptr;
}

// A type §6.22.2's equivalence is judged on here: one written with a type
// keyword and a width the folder can size; a typedef name or a range a
// parameter sets is left alone rather than judged wrongly.
bool IsJudgedType(const DataType& t) {
  return t.kind != DataTypeKind::kNamed && EvalTypeWidth(t) > 0;
}

// §13.5.2 with §6.22.2: a ref argument is matched with an equivalent type.
void CheckRefEquivalence(const RefBinding& b, DiagEngine& diag) {
  if (b.actual->kind != ExprKind::kIdentifier || b.decl.unpacked ||
      !b.formal.unpacked_dims.empty())
    return;
  if (!IsJudgedType(b.formal.data_type) || !IsJudgedType(*b.decl.type)) return;
  if (TypesEquivalent(b.formal.data_type, *b.decl.type)) return;
  diag.Error(b.actual->range.start,
             std::format("ref argument '{}' of '{}' is passed '{}', whose data "
                         "type is not equivalent",
                         b.formal.name, b.func->name, b.actual->text),
             Subclause("13.5.2"));
}

// §13.5.2: a variable, a class property, a member of an unpacked structure or
// an element of an unpacked array is passed by reference, so a select of a
// value with no unpacked dimension is not.
void CheckRefPackedSelect(const RefBinding& b, DiagEngine& diag) {
  if (b.actual->kind != ExprKind::kSelect || b.actual->base != b.root ||
      b.decl.unpacked)
    return;
  diag.Error(b.actual->range.start,
             std::format("a select of packed '{}' cannot be passed by "
                         "reference to argument '{}' of '{}'",
                         b.root->text, b.formal.name, b.func->name),
             Subclause("13.5.2"));
}

// §13.5.2: a ref static argument is passed only what has a static lifetime,
// never an automatic variable or a ref argument without the static qualifier.
void CheckRefStatic(const RefBinding& b, DiagEngine& diag) {
  if (!b.formal.is_ref_static ||
      (!b.decl.automatic && !b.decl.ref_without_static))
    return;
  diag.Error(b.actual->range.start,
             std::format("ref static argument '{}' of '{}' is passed '{}', "
                         "which has no static lifetime",
                         b.formal.name, b.func->name, b.root->text),
             Subclause("13.5.2"));
}

void CheckRefCall(const Expr* call, const RefScope& scope,
                  const FuncDecls& funcs, DiagEngine& diag) {
  auto it = funcs.find(call->callee);
  if (it == funcs.end()) return;
  const ModuleItem* func = it->second;
  size_t positional = call->args.size() - call->arg_names.size();
  for (size_t i = 0; i < positional && i < func->func_args.size(); ++i) {
    const FunctionArg& formal = func->func_args[i];
    const Expr* root = RootIdentifier(call->args[i]);
    if (formal.direction != Direction::kRef || root == nullptr) continue;
    auto decl = scope.find(root->text);
    if (decl == scope.end()) continue;
    RefBinding b{func, formal, call->args[i], root, decl->second};
    CheckRefEquivalence(b, diag);
    CheckRefPackedSelect(b, diag);
    CheckRefStatic(b, diag);
  }
}

struct RefWalk {
  const FuncDecls& funcs;
  DiagEngine& diag;
};

void WalkRefExpr(const Expr* e, const RefScope& scope, const RefWalk& w) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kCall) CheckRefCall(e, scope, w.funcs, w.diag);
  ForEachExprChild(e, [&](const Expr* child) { WalkRefExpr(child, scope, w); });
}

// §6.21: a local is automatic in an automatic subroutine unless declared
// static, and in a static one where declared automatic.
void WalkRefStmt(const Stmt* s, RefScope& scope, bool automatic,
                 const RefWalk& w) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl && !s->var_name.empty()) {
    scope[s->var_name] =
        RefDecl{&s->var_decl_type, !s->var_unpacked_dims.empty(),
                (automatic && !s->var_is_static) || s->var_is_automatic, false};
  }
  ForEachChildExpr(s, [&](Expr* const& e) { WalkRefExpr(e, scope, w); });
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkRefStmt(sub, scope, automatic, w); });
}

void WalkRefSubroutine(const ModuleItem* item, RefScope scope,
                       const RefWalk& w) {
  for (const FunctionArg& arg : item->func_args) {
    scope[arg.name] =
        RefDecl{&arg.data_type, !arg.unpacked_dims.empty(), item->is_automatic,
                arg.direction == Direction::kRef && !arg.is_ref_static};
  }
  for (const Stmt* s : item->func_body_stmts)
    WalkRefStmt(s, scope, item->is_automatic, w);
}

}  // namespace

void Elaborator::ValidateRefArgActuals(const ModuleDecl* decl) {
  RefScope module_scope;
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && !item->name.empty())
      module_scope[item->name] =
          RefDecl{&item->data_type, !item->unpacked_dims.empty(), false, false};
  }
  const RefWalk kWalk{func_decls_, diag_};
  for (const ModuleItem* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      RefScope scope = module_scope;
      WalkRefStmt(item->body, scope, false, kWalk);
    } else if ((item->kind == ModuleItemKind::kTaskDecl ||
                item->kind == ModuleItemKind::kFunctionDecl) &&
               item->method_class.empty()) {
      WalkRefSubroutine(item, module_scope, kWalk);
    }
  }
}

}  // namespace delta
