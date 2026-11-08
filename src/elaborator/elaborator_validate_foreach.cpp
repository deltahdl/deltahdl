#include <algorithm>
#include <cstddef>
#include <format>
#include <iterator>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/parser_token_skips.h"

namespace delta {

namespace {

static std::string_view LvalueRootName(const Expr* e) {
  while (e) {
    switch (e->kind) {
      case ExprKind::kIdentifier:
        return e->text;
      case ExprKind::kSelect:
        e = e->base;
        break;
      case ExprKind::kUnary:
      case ExprKind::kPostfixUnary:
        e = e->lhs ? e->lhs : e->base;
        break;
      default:
        return {};
    }
  }
  return {};
}

static std::string_view ForeachArrayName(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  if (e->kind == ExprKind::kMemberAccess && e->rhs) return e->rhs->text;
  return {};
}

static bool IsIncDecExpr(const Expr* e) {
  if (!e) return false;
  if (e->kind != ExprKind::kUnary && e->kind != ExprKind::kPostfixUnary)
    return false;
  return e->op == TokenKind::kPlusPlus || e->op == TokenKind::kMinusMinus;
}

using LoopVarSet = std::unordered_set<std::string_view>;

struct ForeachArrayDecl {
  const DataType* type;
  size_t unpacked;
};
using ForeachArrays = std::unordered_map<std::string_view, ForeachArrayDecl>;
using ForeachSubroutines =
    std::unordered_map<std::string_view, const ModuleItem*>;

struct ForeachCtx {
  const std::unordered_set<std::string_view>& class_names;
  const ForeachSubroutines& subroutines;
  DiagEngine& diag;
};

static void ReportIfLoopVar(const Expr* target, SourceLoc loc,
                            const LoopVarSet& vars, DiagEngine& diag) {
  auto root = LvalueRootName(target);
  if (root.empty() || !vars.count(root)) return;
  diag.Error(loc,
             std::format("foreach loop variable '{}' is read-only and "
                         "cannot be assigned",
                         root),
             Subclause("12.7.3"));
}

static void ReportLoopVarActuals(const Expr* e, const LoopVarSet& vars,
                                 const ForeachCtx& ctx) {
  auto it = ctx.subroutines.find(e->callee);
  if (it == ctx.subroutines.end()) return;
  const auto& formals = it->second->func_args;
  size_t positional = e->args.size() - e->arg_names.size();
  for (size_t i = 0; i < formals.size(); ++i) {
    Direction dir = formals[i].direction;
    bool writes = dir == Direction::kOutput || dir == Direction::kInout ||
                  (dir == Direction::kRef && !formals[i].is_const);
    int ai = ResolveActualArgIndex(e, i, formals[i].name, positional);
    if (!writes || ai < 0) continue;
    const Expr* actual = e->args[static_cast<size_t>(ai)];
    if (actual) ReportIfLoopVar(actual, actual->range.start, vars, ctx.diag);
  }
}

static void ReportExprWritesToLoopVar(const Expr* e, const LoopVarSet& vars,
                                      const ForeachCtx& ctx) {
  if (!e) return;
  if (IsIncDecExpr(e)) {
    ReportIfLoopVar(e, e->range.start, vars, ctx.diag);
  } else if (e->kind == ExprKind::kBinary &&
             (e->op == TokenKind::kEq || IsCompoundAssignOp(e->op))) {
    ReportIfLoopVar(e->lhs, e->range.start, vars, ctx.diag);
  } else if (e->kind == ExprKind::kCall) {
    ReportLoopVarActuals(e, vars, ctx);
  }
  ForEachExprChild(e, [&](const Expr* child) {
    ReportExprWritesToLoopVar(child, vars, ctx);
  });
}

static void ReportWriteToLoopVar(const Stmt* s, const LoopVarSet& vars,
                                 DiagEngine& diag) {
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign)
    ReportIfLoopVar(s->lhs, s->range.start, vars, diag);
}

static LoopVarSet WithoutDeclaredForVars(const Stmt* s,
                                         const LoopVarSet& vars) {
  LoopVarSet inner = vars;
  for (size_t k = 0; k < s->for_inits.size() && k < s->for_init_types.size();
       ++k) {
    if (s->for_init_types[k].kind == DataTypeKind::kImplicit) continue;
    const Stmt* init = s->for_inits[k];
    if (init && init->lhs && init->lhs->kind == ExprKind::kIdentifier)
      inner.erase(init->lhs->text);
  }
  return inner;
}

static void CheckForeachVarsReadOnly(const Stmt* s, const LoopVarSet& vars,
                                     const ForeachCtx& ctx);

static void CheckBlockStmtsInOrder(const std::vector<Stmt*>& subs,
                                   LoopVarSet& vars, const ForeachCtx& ctx) {
  for (const Stmt* sub : subs) {
    if (sub && sub->kind == StmtKind::kVarDecl) vars.erase(sub->var_name);
    if (vars.empty()) return;
    CheckForeachVarsReadOnly(sub, vars, ctx);
  }
}

static void CheckForeachVarsReadOnly(const Stmt* s, const LoopVarSet& vars,
                                     const ForeachCtx& ctx) {
  if (!s) return;
  ReportWriteToLoopVar(s, vars, ctx.diag);
  if (s->kind == StmtKind::kBlock || s->kind == StmtKind::kFork) {
    LoopVarSet inner = vars;
    CheckBlockStmtsInOrder(s->stmts, inner, ctx);
    CheckBlockStmtsInOrder(s->fork_stmts, inner, ctx);
    return;
  }
  LoopVarSet inner =
      s->kind == StmtKind::kFor ? WithoutDeclaredForVars(s, vars) : vars;
  if (inner.empty()) return;
  ForEachChildExpr(
      s, [&](const Expr* e) { ReportExprWritesToLoopVar(e, inner, ctx); });
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckForeachVarsReadOnly(sub, inner, ctx); });
}

static bool IsIntegralVectorKind(DataTypeKind k) {
  switch (k) {
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kBit:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
      return true;
    default:
      return false;
  }
}

static std::optional<int> ForeachDimCount(
    const ForeachArrayDecl& decl,
    const std::unordered_set<std::string_view>& class_names) {
  static constexpr DataTypeKind kUnpackedOnly[] = {
      DataTypeKind::kReal, DataTypeKind::kShortreal, DataTypeKind::kRealtime,
      DataTypeKind::kChandle, DataTypeKind::kEvent};
  const DataType& t = *decl.type;
  int unpacked = static_cast<int>(decl.unpacked);
  if (IsIntegralVectorKind(t.kind)) {
    return unpacked + (t.packed_dim_left != nullptr ? 1 : 0) +
           static_cast<int>(t.extra_packed_dims.size());
  }
  if (t.kind == DataTypeKind::kString) return unpacked + 1;
  bool is_class = t.kind == DataTypeKind::kNamed && t.scope_name.empty() &&
                  class_names.count(t.type_name) != 0;
  if (is_class ||
      std::ranges::find(kUnpackedOnly, t.kind) != std::end(kUnpackedOnly)) {
    return unpacked;
  }
  return std::nullopt;
}

static void CheckOneForeachStmt(const Stmt* s, const ForeachArrays& arrays,
                                const ForeachCtx& ctx) {
  std::string_view arr_name = ForeachArrayName(s->expr);

  std::unordered_set<std::string_view> named_vars;
  for (auto v : s->foreach_vars) {
    if (v.empty()) continue;
    named_vars.insert(v);
    if (!arr_name.empty() && v == arr_name) {
      ctx.diag.Error(s->range.start,
                     std::format("foreach loop variable '{}' may not have the "
                                 "same name as the array it iterates over",
                                 v),
                     Subclause("12.7.3"));
    }
  }

  if (!named_vars.empty()) CheckForeachVarsReadOnly(s->body, named_vars, ctx);

  if (s->expr->kind != ExprKind::kIdentifier) return;
  auto it = arrays.find(arr_name);
  if (it == arrays.end()) return;
  auto dims = ForeachDimCount(it->second, ctx.class_names);
  if (dims && static_cast<int>(s->foreach_vars.size()) > *dims) {
    ctx.diag.Error(
        s->range.start,
        std::format("foreach lists {} loop variables but array '{}' has "
                    "only {} dimension(s)",
                    s->foreach_vars.size(), arr_name, *dims),
        Subclause("12.7.3"));
  }
}

static void CheckForeachInStmt(const Stmt* s, const ForeachArrays& arrays,
                               const ForeachCtx& ctx);

static void CheckForeachInBlockStmts(const std::vector<Stmt*>& subs,
                                     ForeachArrays& arrays,
                                     const ForeachCtx& ctx) {
  for (const Stmt* sub : subs) {
    if (sub && sub->kind == StmtKind::kVarDecl) {
      arrays.insert_or_assign(
          sub->var_name,
          ForeachArrayDecl{&sub->var_decl_type, sub->var_unpacked_dims.size()});
    }
    CheckForeachInStmt(sub, arrays, ctx);
  }
}

static void CheckForeachInStmt(const Stmt* s, const ForeachArrays& arrays,
                               const ForeachCtx& ctx) {
  if (!s) return;
  if (s->kind == StmtKind::kForeach) CheckOneForeachStmt(s, arrays, ctx);
  if (s->kind == StmtKind::kBlock || s->kind == StmtKind::kFork) {
    ForeachArrays inner = arrays;
    CheckForeachInBlockStmts(s->stmts, inner, ctx);
    CheckForeachInBlockStmts(s->fork_stmts, inner, ctx);
    return;
  }
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckForeachInStmt(sub, arrays, ctx); });
}

static void CheckForeachInSubroutine(const ModuleItem* item,
                                     const ForeachArrays& arrays,
                                     const ForeachCtx& ctx) {
  ForeachArrays inner = arrays;
  for (const auto& arg : item->func_args) {
    inner.insert_or_assign(
        arg.name, ForeachArrayDecl{&arg.data_type, arg.unpacked_dims.size()});
  }
  CheckForeachInBlockStmts(item->func_body_stmts, inner, ctx);
}

static void CheckForeachInClass(const ClassDecl* cls,
                                const ForeachArrays& arrays,
                                const ForeachCtx& ctx) {
  ForeachArrays props = arrays;
  ForeachSubroutines methods = ctx.subroutines;
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kProperty) {
      props.insert_or_assign(
          m->name, ForeachArrayDecl{&m->data_type, m->unpacked_dims.size()});
    } else if (m->kind == ClassMemberKind::kMethod) {
      methods.insert_or_assign(m->method->name, m->method);
    }
  }
  const ForeachCtx kInner{ctx.class_names, methods, ctx.diag};
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod) {
      CheckForeachInSubroutine(m->method, props, kInner);
    } else if (m->kind == ClassMemberKind::kClassDecl) {
      CheckForeachInClass(m->nested_class, props, kInner);
    }
  }
}

bool IsSubroutineItem(const ModuleItem* item) {
  return item->kind == ModuleItemKind::kFunctionDecl ||
         item->kind == ModuleItemKind::kTaskDecl;
}

void AddItemDecl(const ModuleItem* item, ForeachArrays& arrays,
                 ForeachSubroutines& subroutines) {
  if (item->kind == ModuleItemKind::kVarDecl && !item->name.empty()) {
    arrays.emplace(item->name, ForeachArrayDecl{&item->data_type,
                                                item->unpacked_dims.size()});
  } else if (IsSubroutineItem(item)) {
    subroutines.emplace(item->name, item);
  }
}

void CheckForeachInItem(const ModuleItem* item, const ForeachArrays& arrays,
                        const ForeachCtx& ctx) {
  if (item->kind == ModuleItemKind::kClassDecl) {
    CheckForeachInClass(item->class_decl, arrays, ctx);
  } else if (IsProceduralItemKind(item->kind)) {
    CheckForeachInStmt(item->body, arrays, ctx);
  } else if (IsSubroutineItem(item)) {
    CheckForeachInSubroutine(item, arrays, ctx);
  }
}

}  // namespace

void Elaborator::ValidateForeachLoops(const ModuleDecl* decl) {
  CheckForeachLoopsIn(decl->items);
}

void Elaborator::CheckForeachLoopsIn(const std::vector<ModuleItem*>& items) {
  ForeachArrays arrays;
  ForeachSubroutines subroutines;
  for (const auto* item : items) {
    if (item != nullptr) AddItemDecl(item, arrays, subroutines);
  }
  const ForeachCtx kCtx{class_names_, subroutines, diag_};
  for (const auto* item : items) {
    if (item != nullptr) CheckForeachInItem(item, arrays, kCtx);
  }
}

void Elaborator::CheckForeachLoopsInClass(const ClassDecl* cls) {
  const ForeachSubroutines kNone;
  CheckForeachInClass(cls, ForeachArrays{},
                      ForeachCtx{class_names_, kNone, diag_});
}

}  // namespace delta
