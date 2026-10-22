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

// §12.7.3 — the identifier reached by descending an lvalue through index
// selects and increment/decrement operators: the variable an assignment
// writes, whole or in part. A member access ends the descent with no name,
// since §12.7.3 gives a loop variable over an associative array indexed by a
// specific type that index type, and through a class handle a member write
// reaches the object the handle refers to, not the handle (§8.3); UVM's
// uvm_phase.svh writes `pred.m_successors[begin_node] = 1;` inside
// `foreach (m_predecessors[pred])`. A struct-typed index whose member is
// written goes unreported here, the check naming variables without types.
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

// §12.7.3 — the identifier naming the array a foreach iterates over. For a
// hierarchical designator (a.b.arr) this is the trailing member name.
// The array's own identifier: the name itself, or the last member of the
// chain Parser::ParseForeachArrayId reads a hierarchical or scoped name into.
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

// §12.7.3: what the dimension rule reads of an array's declaration, the type it
// was declared with and the number of unpacked dimensions written after its
// name. A module's or a package's variable, a block's or a subroutine's local,
// a subroutine's formal and a class property each carry both.
struct ForeachArrayDecl {
  const DataType* type;
  size_t unpacked;
};
using ForeachArrays = std::unordered_map<std::string_view, ForeachArrayDecl>;
using ForeachSubroutines =
    std::unordered_map<std::string_view, const ModuleItem*>;

// What the §12.7.3 walks read besides the statement in hand: the classes a
// declared type may name, the subroutines a call in the scope may name, and
// where the reports go.
struct ForeachCtx {
  const std::unordered_set<std::string_view>& class_names;
  const ForeachSubroutines& subroutines;
  DiagEngine& diag;
};

// §12.7.3 — reports `target`, an lvalue written at `loc`, where it is one of
// `vars` or part of one.
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

// §13.5: the actuals of call `e` the subroutine it names may write, those
// bound to an output, an inout or a ref formal that is not `const ref`, each
// reported where it is one of `vars`. A call whose subroutine is not declared
// in the scope is left alone.
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

// §12.7.3 with §11.4.1 and §11.4.2 — the writes expression `e` makes inside
// itself: an increment or a decrement writes its operand, a parenthesized
// assignment operator its left operand, and a call the actuals of its writing
// formals. Every child is descended, so a write is found wherever in the
// expression it stands.
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

// §12.7.3 — reports statement `s` where it is an assignment statement whose
// target is one of `vars`. The writes its expressions make are
// ReportExprWritesToLoopVar's, an increment written as a whole statement among
// them.
static void ReportWriteToLoopVar(const Stmt* s, const LoopVarSet& vars,
                                 DiagEngine& diag) {
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign)
    ReportIfLoopVar(s->lhs, s->range.start, vars, diag);
}

// §12.7.1 — the names a for loop declares as its control variables, removed
// from `vars`: the loop creates an implicit block around itself, so a declared
// name that is a loop variable's is another variable in the loop's
// initialization, condition, step and body; UVM's uvm_reg.svh writes
// `for (int i = ...; i < top; i++)` inside `foreach (m_fields[i])`. A plain
// `for (i = 0; ...)` declares nothing and writes the loop variable.
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

// §6.21 — walks a block's statements in order: a variable declared in a block
// is local to it and to the blocks nested below, from its declaration on, so
// a block-item declaration of a loop variable's name ends the rule for that
// name in the rest of the block.
static void CheckBlockStmtsInOrder(const std::vector<Stmt*>& subs,
                                   LoopVarSet& vars, const ForeachCtx& ctx) {
  for (const Stmt* sub : subs) {
    if (sub && sub->kind == StmtKind::kVarDecl) vars.erase(sub->var_name);
    if (vars.empty()) return;
    CheckForeachVarsReadOnly(sub, vars, ctx);
  }
}

// §12.7.3 — foreach loop variables are read-only. Reports every write the loop
// body makes to one of `vars`: an assignment statement's, and one made inside
// any expression a statement holds.
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
  // Every member of Stmt that holds an expression or a statement, taken from
  // ForEachChildExpr and ForEachChildStmt in elaborator_validate_internal.h
  // rather than listed again here. §12.7.3 makes the loop variable read-only
  // for the whole of the loop body, so a member these walks miss is a position
  // a write to one goes unreported. Nothing stops early: the clause is broken
  // once per write, and each write is reported where it stands.
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

// §12.7.3 — the number of dimensions a foreach can address on an array whose
// declaration settles it, or nullopt where it does not. An integral element
// type's packed dimensions count with the unpacked ones. A string element is a
// dynamic array of bytes, so its characters are one dimension more after the
// unpacked ones. A real, chandle, event or class handle element has no packed
// dimension, so the unpacked ones are all. A typedef'd or aggregate element
// type may contribute packed dimensions the declaration does not show, so it
// is left alone.
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

// §12.7.3 — applies the foreach-loop semantic rules to a single foreach
// statement `s` (already known to be StmtKind::kForeach), whose array is
// looked up in `arrays`, the declarations in scope where the loop stands.
static void CheckOneForeachStmt(const Stmt* s, const ForeachArrays& arrays,
                                const ForeachCtx& ctx) {
  std::string_view arr_name = ForeachArrayName(s->expr);

  std::unordered_set<std::string_view> named_vars;
  for (auto v : s->foreach_vars) {
    if (v.empty()) continue;
    named_vars.insert(v);
    // A loop variable shall not reuse the array's identifier.
    if (!arr_name.empty() && v == arr_name) {
      ctx.diag.Error(s->range.start,
                     std::format("foreach loop variable '{}' may not have the "
                                 "same name as the array it iterates over",
                                 v),
                     Subclause("12.7.3"));
    }
  }

  if (!named_vars.empty()) CheckForeachVarsReadOnly(s->body, named_vars, ctx);

  // The loop-variable count may not exceed the array's dimensionality. Only a
  // plain identifier names a declaration `arrays` holds; the array a member
  // access reaches is declared in the scope the access leads into.
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

// §6.21 — a block's statements in order, each declaration putting its name in
// `arrays` from there on, where it hides a declaration of the same name made
// outside the block.
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

// §12.7.3 — applies the foreach-loop semantic rules to every foreach statement
// reachable from `s`.
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
  // Every member of Stmt that holds a statement, taken from ForEachChildStmt
  // in elaborator_validate_internal.h rather than listed again here. A foreach
  // is a statement like any other, so which member holds it says nothing about
  // whether §12.7.3 covers it, and a member this walk misses is a foreach the
  // clause is not applied to.
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckForeachInStmt(sub, arrays, ctx); });
}

// A subroutine's body, with its formals and then its body's declarations in
// scope over the declarations of `arrays`.
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

// §8.10 — a class's methods, with its properties in scope over `arrays` and
// its methods callable beside the subroutines of `ctx`. A nested class (§8.23)
// is walked the same way inside it.
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

// The array or the subroutine `item` declares, put in `arrays` or
// `subroutines`.
void AddItemDecl(const ModuleItem* item, ForeachArrays& arrays,
                 ForeachSubroutines& subroutines) {
  if (item->kind == ModuleItemKind::kVarDecl && !item->name.empty()) {
    arrays.emplace(item->name, ForeachArrayDecl{&item->data_type,
                                                item->unpacked_dims.size()});
  } else if (IsSubroutineItem(item)) {
    subroutines.emplace(item->name, item);
  }
}

// The bodies `item` owns: a class's methods, a procedural block's statement
// and a subroutine's.
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

// §12.7.3 names no enclosing declaration the rule is suspended in, so every
// body a declaration of `items` owns is walked: a procedural block's, a
// subroutine's and each class method's. The dimension rule reads the array
// declaration in scope where the foreach stands, so the walk carries the
// declarations from the scope of `items` inward, through a class's properties,
// a subroutine's formals and each block's own declarations, and a nearer one
// hides a farther one of the same name. A name with no declaration in scope is
// left alone.
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
