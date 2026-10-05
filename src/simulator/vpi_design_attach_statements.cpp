#include <cstddef>
#include <initializer_list>
#include <string>
#include <string_view>
#include <vector>

#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// §11.4.1: whether `stmt` is written with an assignment operator such as +=.
// The parser writes `a op= b` as an assignment of `a op b` whose operation's
// left operand is the very expression the assignment's left side is, which an
// assignment written out as `a = a op b` never has.
bool IsOperatorAssignment(const Stmt& stmt) {
  return stmt.rhs != nullptr && stmt.rhs->kind == ExprKind::kBinary &&
         stmt.lhs != nullptr && stmt.rhs->lhs == stmt.lhs;
}

// The spelling of the operator `op`, which TokenKindName gives between quotes.
std::string_view OperatorSpelling(TokenKind op) {
  std::string_view name = TokenKindName(op);
  if (name.size() >= 2 && name.front() == '\'' && name.back() == '\'') {
    name = name.substr(1, name.size() - 2);
  }
  return name;
}

// §37.59: an operation of `op_type` over `operands`, in order; null where an
// operand is not modelled, since an operation missing one would stand for an
// expression the source never wrote.
VpiObject* MakeOperation(int op_type,
                         std::initializer_list<VpiObject*> operands,
                         const VpiAttachBuild& build) {
  for (const VpiObject* operand : operands) {
    if (operand == nullptr) return nullptr;
  }
  VpiObject* op = build.alloc();
  op->type = vpiOperation;
  op->op_type = op_type;
  op->children.assign(operands.begin(), operands.end());
  return op;
}

// §9.4.2 with §37.59: the expression one event of an event control is
// written as - the expression, net, variable or named event it names, under
// the posedge or negedge operation its edge makes, and under the iff
// operation where a condition guards it. A sequence (§9.4.2.4) and the edge
// keyword, which §37.59 gives no operation of its own, are not modelled.
VpiObject* EventItem(const EventExpr& event, const VpiStmtBuild& with) {
  if (event.is_sequence_event || event.edge == Edge::kEdge) return nullptr;
  VpiObject* item = with.expression(event.signal);
  if (event.edge != Edge::kNone) {
    item = MakeOperation(
        event.edge == Edge::kPosedge ? vpiPosedgeOp : vpiNegedgeOp, {item},
        with.build);
  }
  if (event.iff_condition != nullptr) {
    item = MakeOperation(vpiIffOp, {item, with.expression(event.iff_condition)},
                         with.build);
  }
  return item;
}

// §37.65: the condition an event control is written over. §9.4.2.1 joins the
// events of a list with `or`, a comma meaning the same, and the grammar nests
// each `or` around the events before it, so the condition is the event or
// operation of the list so far and the next event. Null where an event is not
// modelled, and for the implicit event list of §9.4.2.2, which writes none.
VpiObject* EventCondition(const std::vector<EventExpr>& events,
                          const VpiStmtBuild& with) {
  VpiObject* condition = nullptr;
  for (const EventExpr& event : events) {
    VpiObject* item = EventItem(event, with);
    if (item == nullptr) return nullptr;
    condition =
        condition == nullptr
            ? item
            : MakeOperation(vpiEventOrOp, {condition, item}, with.build);
  }
  return condition;
}

// A timing control of `type` hung from `holder`, reaching `operand`: the
// condition of an event control (§37.65), the delay of a delay control
// (§37.68), or the count of a repeat control (§37.69).
VpiObject* MakeControl(int type, VpiObject* holder, VpiObject* operand,
                       const VpiAttachBuild& build) {
  VpiObject* control = build.alloc();
  control->type = type;
  control->parent = holder;
  if (operand != nullptr) control->children.push_back(operand);
  holder->children.push_back(control);
  return control;
}

// §37.64 with §9.4.5: the timing control written inside the assignment
// `obj` stands for, hung from it - a delay control, an event control, or a
// repeat control reaching the event control it repeats (§37.69). Details 1 of
// §37.65 and §37.68 have such a control guard no statement of its own.
void MakeIntraAssignmentControl(VpiObject* obj, const Stmt& stmt,
                                const VpiStmtBuild& with) {
  if (stmt.delay != nullptr) {
    MakeControl(vpiDelayControl, obj, with.expression(stmt.delay), with.build);
  } else if (stmt.repeat_event_count != nullptr) {
    VpiObject* repeat =
        MakeControl(vpiRepeatControl, obj,
                    with.expression(stmt.repeat_event_count), with.build);
    MakeControl(vpiEventControl, repeat, EventCondition(stmt.events, with),
                with.build);
  } else if (!stmt.events.empty()) {
    MakeControl(vpiEventControl, obj, EventCondition(stmt.events, with),
                with.build);
  }
}

// §37.64: an assignment's two sides, its operator - detail 1's vpiAssignmentOp
// for `=` and `<=`, and for an assignment operator the operator it combines
// with the assignment, the right side being the operand written - whether it
// blocks, and the timing control written inside it.
void FillAssignment(VpiObject* obj, const Stmt& stmt,
                    const VpiStmtBuild& with) {
  const bool kOperator = IsOperatorAssignment(stmt);
  obj->lhs = with.expression(stmt.lhs);
  obj->rhs = with.expression(kOperator ? stmt.rhs->rhs : stmt.rhs);
  obj->op_type = kOperator ? VpiAssignmentOpType(OperatorSpelling(stmt.rhs->op))
                           : vpiAssignmentOp;
  obj->blocking = stmt.kind == StmtKind::kBlockingAssign;
  MakeIntraAssignmentControl(obj, stmt, with);
}

// `child` among the children of `obj`, where one was made.
void AddChild(VpiObject* obj, VpiObject* child) {
  if (child != nullptr) obj->children.push_back(child);
}

// §37.71 and §37.72: the qualifier a unique, unique0 or priority keyword gives
// an if or case statement, with §37.72's inside and tagged bits for a case
// inside (§12.5.4) and a case matches (§12.6.1). Annex M gives unique0 no bit
// of its own; §12.4.2 makes it a unique that reports no violation where no
// branch matches, so it reports the unique bit.
int QualifierOf(const Stmt& stmt) {
  int qualifier = vpiNoQualifier;
  if (stmt.qualifier == CaseQualifier::kUnique ||
      stmt.qualifier == CaseQualifier::kUnique0) {
    qualifier |= vpiUniqueQualifier;
  } else if (stmt.qualifier == CaseQualifier::kPriority) {
    qualifier |= vpiPriorityQualifier;
  }
  if (stmt.case_inside) qualifier |= vpiInsideQualifier;
  if (stmt.case_matches) qualifier |= vpiTaggedQualifier;
  return qualifier;
}

// §37.72: a case statement's type, the keyword it opens with, its qualifier,
// the expression it selects on, and an item per case item of §12.5 grouping
// the expressions that branch to its statement (detail 1); a default item
// groups none (detail 2).
void FillCase(VpiObject* obj, const Stmt& stmt, const VpiStmtBuild& with) {
  obj->case_type = stmt.case_kind == TokenKind::kKwCasex   ? vpiCaseX
                   : stmt.case_kind == TokenKind::kKwCasez ? vpiCaseZ
                                                           : vpiCaseExact;
  obj->qualifier = QualifierOf(stmt);
  AddChild(obj, with.expression(stmt.condition));
  for (const CaseItem& item : stmt.case_items) {
    VpiObject* made = with.build.alloc();
    made->type = vpiCaseItem;
    made->parent = obj;
    made->process = obj->process;
    made->default_case_item = item.is_default;
    obj->children.push_back(made);
    for (const Expr* pattern : item.patterns) {
      AddChild(made, with.expression(pattern));
    }
    with.statement(item.body, made);
  }
}

// §37.74: the statements one part of a for header writes, built under the for
// statement and held apart from its children, where the body is looked for.
std::vector<VpiObject*> HeaderStmts(VpiObject* obj,
                                    const std::vector<Stmt*>& stmts,
                                    const VpiStmtBuild& with) {
  const std::size_t kBefore = obj->children.size();
  for (const Stmt* header : stmts) with.statement(header, obj);
  const auto kFirst =
      obj->children.begin() + static_cast<std::ptrdiff_t>(kBefore);
  std::vector<VpiObject*> made(kFirst, obj->children.end());
  obj->children.erase(kFirst, obj->children.end());
  return made;
}

// §37.74: a for statement's header, its condition and its body, and whether
// it declares its loop variables, which §37.12 detail 2 makes it a scope for.
void FillFor(VpiObject* obj, const Stmt& stmt, const VpiStmtBuild& with) {
  obj->local_var_decls =
      !stmt.for_init_types.empty() &&
      stmt.for_init_types.front().kind != DataTypeKind::kImplicit;
  AddChild(obj, with.expression(stmt.for_cond));
  obj->for_init_stmts = HeaderStmts(obj, stmt.for_inits, with);
  obj->for_inc_stmts = HeaderStmts(obj, stmt.for_steps, with);
  obj->body = with.statement(stmt.for_body, obj);
}

// §37.75: the array a foreach statement indexes (detail 1), its index
// variables in order with none for one skipped (detail 2), and its body.
// §12.7.3 declares each index variable of the statement with the type of the
// array's index: the index type for an associative first dimension, int for
// every other.
void FillForeach(VpiObject* obj, const Stmt& stmt, const VpiStmtBuild& with) {
  obj->foreach_array = with.expression(stmt.expr);
  for (std::string_view name : stmt.foreach_vars) {
    VpiObject* var = nullptr;
    if (!name.empty()) {
      var = with.build.alloc();
      var->type =
          obj->loop_vars.empty() ? with.index_kind(stmt.expr) : vpiIntVar;
      var->name = with.build.keep(std::string(name));
      var->parent = obj;
    }
    obj->loop_vars.push_back(var);
  }
  obj->body = with.statement(stmt.body, obj);
}

// §37.67: an ordered wait's events, in order, and the statements of its
// action block, the else action second.
void FillOrderedWait(VpiObject* obj, const Stmt& stmt,
                     const VpiStmtBuild& with) {
  for (const Expr* event : stmt.wait_order_events) {
    AddChild(obj, with.expression(event));
  }
  with.statement(stmt.then_branch, obj);
  with.statement(stmt.else_branch, obj);
}

// The objects a statement holding a condition and the statements it runs
// reaches: §37.66's while and repeat, §37.67's wait, §37.70's forever,
// §37.71's if and if-else, and §37.75's do-while.
void FillConditional(VpiObject* obj, const Stmt& stmt,
                     const VpiStmtBuild& with) {
  if (stmt.kind == StmtKind::kIf) obj->qualifier = QualifierOf(stmt);
  AddChild(obj, with.expression(stmt.condition));
  if (stmt.kind == StmtKind::kIf) {
    with.statement(stmt.then_branch, obj);
    with.statement(stmt.else_branch, obj);
    return;
  }
  obj->body = with.statement(stmt.body, obj);
}

// The components of the hierarchical name `expr` is written as, outermost
// first; false for an expression that is no such name.
bool NameParts(const Expr* expr, std::vector<std::string_view>& parts) {
  if (expr == nullptr) return false;
  if (expr->kind == ExprKind::kIdentifier) {
    parts.push_back(expr->text);
    return true;
  }
  if (expr->kind != ExprKind::kMemberAccess || expr->rhs == nullptr ||
      !NameParts(expr->lhs, parts)) {
    return false;
  }
  parts.push_back(expr->rhs->text);
  return true;
}

// §37.77 with §9.6.2: the task, function, named begin or named fork the
// disable written as `name` names, the name resolved upward from `from`, the
// block or statement the disable stands in (§23.8): the first component is a
// scope around the statement of that name, which is how a block disables
// itself, or one a scope around it holds, and each further component is held
// by the one before. Null where the name reaches none of the four.
VpiObject* DisableTarget(VpiObject* from, const Expr* name) {
  std::vector<std::string_view> parts;
  if (!NameParts(name, parts)) return nullptr;
  for (VpiObject* scope = from; scope != nullptr; scope = scope->parent) {
    VpiObject* found =
        scope->name == parts.front() ? scope : ChildNamed(scope, parts.front());
    for (std::size_t i = 1; found != nullptr && i < parts.size(); ++i) {
      found = ChildNamed(found, parts[i]);
    }
    if (found != nullptr && VpiIsDisableTargetType(found->type)) return found;
  }
  return nullptr;
}

}  // namespace

VpiObject* VpiEventCondition(const std::vector<EventExpr>& events,
                             const VpiStmtBuild& with) {
  return EventCondition(events, with);
}

int VpiBuiltStmtKind(const Stmt& stmt) {
  switch (stmt.kind) {
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
      return vpiAssignment;
    case StmtKind::kEventControl:
      return vpiEventControl;
    case StmtKind::kDelay:
      return vpiDelayControl;
    case StmtKind::kAssign:
      return vpiAssignStmt;
    case StmtKind::kDeassign:
      return vpiDeassign;
    case StmtKind::kForce:
      return vpiForce;
    case StmtKind::kRelease:
      return vpiRelease;
    case StmtKind::kIf:
      return stmt.else_branch != nullptr ? vpiIfElse : vpiIf;
    case StmtKind::kCase:
      return vpiCase;
    case StmtKind::kForever:
      return vpiForever;
    case StmtKind::kWhile:
      return vpiWhile;
    case StmtKind::kRepeat:
      return vpiRepeat;
    case StmtKind::kDoWhile:
      return vpiDoWhile;
    case StmtKind::kFor:
      return vpiFor;
    case StmtKind::kForeach:
      return vpiForeachStmt;
    case StmtKind::kWait:
      return vpiWait;
    case StmtKind::kWaitFork:
      return vpiWaitFork;
    case StmtKind::kWaitOrder:
      return vpiOrderedWait;
    case StmtKind::kDisable:
      return vpiDisable;
    case StmtKind::kDisableFork:
      return vpiDisableFork;
    default:
      return 0;
  }
}

void VpiFillStmt(VpiObject* obj, const Stmt& stmt, const VpiStmtBuild& with) {
  switch (stmt.kind) {
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
      FillAssignment(obj, stmt, with);
      return;
    case StmtKind::kEventControl:
      // §37.65: the condition the control waits on, which an implicit event
      // list leaves unwritten, and the statement it guards.
      AddChild(obj, stmt.is_star_event ? nullptr
                                       : EventCondition(stmt.events, with));
      obj->body = with.statement(stmt.body, obj);
      return;
    case StmtKind::kDelay:
      // §37.68: the delay the control waits, reached through vpiDelay, and the
      // statement it delays.
      AddChild(obj, with.expression(stmt.delay));
      obj->body = with.statement(stmt.body, obj);
      return;
    case StmtKind::kAssign:
    case StmtKind::kDeassign:
    case StmtKind::kForce:
    case StmtKind::kRelease:
      // §37.79: the target an assign, deassign, force or release names, and
      // the expression an assign or force drives it with.
      obj->lhs = with.expression(stmt.lhs);
      obj->rhs = with.expression(stmt.rhs);
      return;
    case StmtKind::kCase:
      FillCase(obj, stmt, with);
      return;
    case StmtKind::kFor:
      FillFor(obj, stmt, with);
      return;
    case StmtKind::kForeach:
      FillForeach(obj, stmt, with);
      return;
    case StmtKind::kWaitOrder:
      FillOrderedWait(obj, stmt, with);
      return;
    case StmtKind::kDisable:
      obj->disable_target = DisableTarget(obj->parent, stmt.expr);
      return;
    case StmtKind::kWaitFork:
    case StmtKind::kDisableFork:
      return;
    default:
      FillConditional(obj, stmt, with);
      return;
  }
}

}  // namespace delta
