#include <initializer_list>
#include <string_view>
#include <vector>

#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
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

}  // namespace

int VpiControlOrAssignKind(const Stmt& stmt) {
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
    default:
      return 0;
  }
}

void VpiFillControlOrAssign(VpiObject* obj, const Stmt& stmt,
                            const VpiStmtBuild& with) {
  switch (stmt.kind) {
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
      FillAssignment(obj, stmt, with);
      return;
    case StmtKind::kEventControl: {
      // §37.65: the condition the control waits on, which an implicit event
      // list leaves unwritten.
      VpiObject* condition =
          stmt.is_star_event ? nullptr : EventCondition(stmt.events, with);
      if (condition != nullptr) obj->children.push_back(condition);
      return;
    }
    case StmtKind::kDelay: {
      // §37.68: the delay the control waits, reached through vpiDelay.
      VpiObject* delay = with.expression(stmt.delay);
      if (delay != nullptr) obj->children.push_back(delay);
      return;
    }
    default:
      // §37.79: the target an assign, deassign, force or release names, and
      // the expression an assign or force drives it with.
      obj->lhs = with.expression(stmt.lhs);
      obj->rhs = with.expression(stmt.rhs);
      return;
  }
}

}  // namespace delta
