#include "simulator/vpi.h"
// §37.65 detail 1's named event and §37.69's repeat control are defined in the
// SystemVerilog VPI header alongside the timing-control kinds themselves.
#include "simulator/sv_vpi_user.h"
// §37.4.1's `stmt` class predicate, which tells the statement a control guards
// from its other children, is declared here.
#include "simulator/vpi_internal.h"

namespace delta {

// ===========================================================================
// §37.65 Event control, §37.68 Delay control, §37.69 Repeat control. The three
// timing controls §37.64 draws an assignment reaching, which are read together
// because the repeat control reaches an event control and both of the others
// answer the same pair of questions: what the control is written over, and what
// statement it governs. They sit in a file of their own because the statement
// helpers they were written beside had grown past the length
// .github/workflows/deltahdl.yml admits a source file.
// ===========================================================================

VpiHandle VpiEventControlStmt(VpiHandle event_control) {
  // §37.65 detail 1: an event control reaches the statement it guards through
  // vpiStmt. When the event control is associated with an assignment - i.e. it
  // is the event control drawn on an assignment object (§37.64) - that
  // statement is always null, since the assignment itself is the action and
  // there is no separate guarded statement. For any other event control the
  // first statement child is returned, or null when none is attached.
  //
  // §37.4.1 makes the dotted `stmt` enclosure the guarded statement is drawn in
  // a class grouping other objects rather than a kind of its own, so the
  // statement is found by being one of the kinds it groups. Asking for a child
  // whose own type is vpiStmt asked for the relation tag, which is a kind no
  // statement carries.
  if (!event_control) return nullptr;
  if (event_control->parent && event_control->parent->type == vpiAssignment) {
    return nullptr;
  }
  for (auto* child : event_control->children) {
    if (VpiIsScopeBodyStmtType(child->type)) return child;
  }
  return nullptr;
}

VpiHandle VpiEventControlConditionExpr(VpiHandle event_control) {
  // §37.65: an event control "@" reaches its controlling condition through
  // vpiCondition. The diagram routes that edge to one of three operand kinds -
  // an expression (e.g. "@(a or b)", "@(posedge clk)"), a sequence instance
  // (e.g. "@(seq)"), or a named event (e.g. "@ev"). The condition is therefore
  // the first child whose own type is one of those kinds, never the
  // vpiCondition relation tag itself, which is why the generic child walk
  // cannot serve it. The guarded body is a statement child and is skipped by
  // this scan. Null when no condition operand is attached.
  if (!event_control) return nullptr;
  for (auto* child : event_control->children) {
    if (VpiIsExprType(child->type) || child->type == vpiSequenceInst ||
        child->type == vpiNamedEvent) {
      return child;
    }
  }
  return nullptr;
}

VpiHandle VpiRepeatControlExpr(VpiHandle repeat_control) {
  // §37.69: a repeat control reaches its count expression through the diagram's
  // unlabeled edge to an expr - the vpiExpr relation. The count is the
  // repetition number of an intra-assignment repeat event control ("repeat (n)
  // @(event)"). Its own type is an expression kind - an operation, a constant,
  // a reference, a parameter or either kind of select - rather than the vpiExpr
  // relation tag, so it is found by scanning for the first expression child;
  // null when none is attached. The repeat
  // control's other unlabeled edge, to the event control, reaches a child whose
  // own type is vpiEventControl and is left to the generic traversal.
  if (!repeat_control) return nullptr;
  for (auto* child : repeat_control->children) {
    if (VpiIsExprType(child->type)) return child;
  }
  return nullptr;
}

VpiHandle VpiDelayControlStmt(VpiHandle delay_control) {
  // §37.68 detail 1: a delay control reaches the statement it guards through
  // vpiStmt. When the delay control is associated with an assignment - i.e. it
  // is the delay control drawn on an assignment object (§37.64) - that
  // statement is always null, since the assignment itself is the action and
  // there is no separate guarded statement. For any other delay control the
  // first statement child is returned, or null when none is attached, and it is
  // found by being one of the kinds §37.4.1's `stmt` class groups rather than
  // by carrying the relation's own tag, which is a kind no statement carries.
  if (!delay_control) return nullptr;
  if (delay_control->parent && delay_control->parent->type == vpiAssignment) {
    return nullptr;
  }
  for (auto* child : delay_control->children) {
    if (VpiIsScopeBodyStmtType(child->type)) return child;
  }
  return nullptr;
}

VpiHandle VpiDelayControlDelayExpr(VpiHandle delay_control) {
  // §37.68: a delay control "#" reaches the expression giving its delay through
  // the vpiDelay relation - the "#" operand ("#5", "#(a+b)", "#dly"). That edge
  // holds whether or not the delay control is associated with an assignment: an
  // intra-assignment delay ("x = #5 y") reports a null guarded statement
  // (detail 1) yet still carries a delay expression, so this scan does not
  // apply the assignment-association carve-out that VpiDelayControlStmt does.
  // The delay operand is the delay control's first child whose own type is an
  // expression kind (a constant, an operation, a reference, ...) - never the
  // guarded statement child (a vpiStmt) and never the vpiDelay relation tag
  // itself, which is why the generic child walk keyed on the relation enum
  // cannot serve it. Null when no delay operand is attached.
  if (!delay_control) return nullptr;
  for (auto* child : delay_control->children) {
    if (VpiIsExprType(child->type)) return child;
  }
  return nullptr;
}

}  // namespace delta
