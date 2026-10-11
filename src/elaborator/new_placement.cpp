#include "elaborator/new_placement.h"

#include <cstddef>
#include <format>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/queue_dim.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// What a variable's declaration says of its shape: the type written and the
// unpacked dimensions after its name.
struct DeclaredShape {
  const DataType* type;
  const std::vector<Expr*>* dims;
};

using DeclaredShapes = std::unordered_map<std::string_view, DeclaredShape>;

}  // namespace

// `new` and `C::new` alike; neither is an expression.
static bool IsNew(const Expr* e) {
  return e->kind == ExprKind::kCall && e->text == "new";
}

// The first `new` written within `e`, `e` itself included. A call's arguments
// are not searched: a `new` among them is the parser's to report.
static const Expr* NewWithin(const Expr* e) {
  if (e == nullptr) return nullptr;
  if (IsNew(e)) return e;
  if (e->kind == ExprKind::kCall) return nullptr;
  const Expr* found = nullptr;
  AnyExprChild(e, [&found](const Expr* child) {
    found = NewWithin(child);
    return found != nullptr;
  });
  return found;
}

static void ReportMisplacedNew(const Expr* where, DiagEngine& diag) {
  diag.Error(where->range.start,
             "'new' stands only as the whole right-hand side of a blocking "
             "assignment or a declaration assignment",
             Subclause("7.5.1"));
}

// A right-hand side on which no `new` may stand at all.
static void CheckNoNew(const Expr* rhs, DiagEngine& diag) {
  if (const Expr* found = NewWithin(rhs)) ReportMisplacedNew(found, diag);
}

// Whether a variable of `shape`, selected `depth` times, is something no `new`
// constructs: an element that the declaration gives a fixed-size or
// associative dimension, or one with no dimension left whose type is a
// keyword. A dynamic dimension is the parser's null, and a queue's is sized by
// `new []` as §7.10.5's bounded queues are; a named type may be a class or a
// typedef of a dynamic array.
static bool NewCannotConstruct(const DeclaredShape& shape, size_t depth) {
  if (depth < shape.dims->size()) {
    const Expr* dim = (*shape.dims)[depth];
    return dim != nullptr && !IsQueueDim(dim);
  }
  return shape.type->kind != DataTypeKind::kNamed;
}

// A right-hand side that is a `new` as a whole is judged against the variable
// the left-hand side names, when it names one this walk has seen declared; any
// other `new` within it is an operand.
static void CheckAssignedNew(const Expr* lhs, std::string_view declared,
                             const Expr* rhs, const DeclaredShapes& shapes,
                             DiagEngine& diag) {
  const Expr* found = NewWithin(rhs);
  if (found == nullptr) return;
  if (found != rhs) {
    ReportMisplacedNew(found, diag);
    return;
  }
  size_t depth = 0;
  for (; lhs != nullptr && lhs->kind == ExprKind::kSelect; lhs = lhs->base) {
    ++depth;
  }
  if (lhs != nullptr && lhs->kind == ExprKind::kIdentifier)
    declared = lhs->text;
  auto it = shapes.find(declared);
  if (it == shapes.end() || !NewCannotConstruct(it->second, depth)) return;
  diag.Error(rhs->range.start,
             std::format("'new' is assigned to '{}', which is neither a "
                         "dynamic array nor a class handle",
                         declared),
             Subclause("7.5.1"));
}

static void CheckStmt(const Stmt* s, DeclaredShapes& shapes, DiagEngine& diag) {
  if (s == nullptr) return;
  switch (s->kind) {
    case StmtKind::kVarDecl:
      shapes[s->var_name] = {&s->var_decl_type, &s->var_unpacked_dims};
      if (s->var_init != nullptr) {
        CheckAssignedNew(nullptr, s->var_name, s->var_init, shapes, diag);
      }
      break;
    case StmtKind::kBlockingAssign:
      // Syntax 10-2 (printed page 252): only the expression form of a
      // blocking assignment takes a delay or event control, and the forms that
      // assign a dynamic_array_new or a class_new take none.
      if ((s->delay != nullptr || !s->events.empty()) &&
          NewWithin(s->rhs) == s->rhs) {
        diag.Error(s->range.start,
                   "an assignment of 'new' takes no intra-assignment delay "
                   "or event control",
                   Subclause("10.4"));
      }
      CheckAssignedNew(s->lhs, {}, s->rhs, shapes, diag);
      break;
    case StmtKind::kNonblockingAssign:
      CheckNoNew(s->rhs, diag);
      break;
    default:
      break;
  }
  ForEachChildStmt(
      s, [&shapes, &diag](Stmt* const& sub) { CheckStmt(sub, shapes, diag); });
}

// A subroutine's arguments are declarations its body's assignments may name.
static void CheckSubroutine(const ModuleItem* item, DeclaredShapes shapes,
                            DiagEngine& diag) {
  for (const FunctionArg& arg : item->func_args) {
    shapes[arg.name] = {&arg.data_type, &arg.unpacked_dims};
  }
  for (const Stmt* s : item->func_body_stmts) CheckStmt(s, shapes, diag);
}

void CheckNewPlacement(const ModuleDecl* decl, DiagEngine& diag) {
  DeclaredShapes module_shapes;
  for (const ModuleItem* item : decl->items) {
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    module_shapes[item->name] = {&item->data_type, &item->unpacked_dims};
    if (item->init_expr != nullptr) {
      CheckAssignedNew(nullptr, item->name, item->init_expr, module_shapes,
                       diag);
    }
  }
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckNoNew(item->assign_rhs, diag);
    } else if (IsProceduralItemKind(item->kind)) {
      DeclaredShapes shapes = module_shapes;
      CheckStmt(item->body, shapes, diag);
    } else if (item->kind == ModuleItemKind::kFunctionDecl ||
               item->kind == ModuleItemKind::kTaskDecl) {
      CheckSubroutine(item, module_shapes, diag);
    }
  }
}

}  // namespace delta
