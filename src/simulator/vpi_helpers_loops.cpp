#include <vector>

#include "simulator/vpi.h"

namespace delta {

// ===========================================================================
// §37.66 While, repeat, §37.74 For, §37.75 Do-while. The loop statements whose
// object model draws a controlling condition and the statements a loop header
// writes beside the body it runs. They sit in a file of their own because the
// statement helpers they were written beside had grown past the length
// .github/workflows/deltahdl.yml admits a source file.
// ===========================================================================

bool VpiIsWhileOrRepeatType(int type) {
  // §37.66: the two looping statements the while/repeat diagram groups together
  // - a while statement and a repeat statement. Both reach a controlling
  // condition expression (vpiCondition) and a body statement (vpiStmt) through
  // the same relations.
  return type == vpiWhile || type == vpiRepeat;
}

VpiHandle VpiLoopConditionExpr(VpiHandle loop) {
  // §37.66: a while or repeat statement reaches its controlling condition
  // through vpiCondition. The condition is an expression child whose own type
  // is an expression kind (an operation, a reference, a constant, ...) rather
  // than the vpiCondition relation tag, so it is found by scanning for the
  // first expression child. Null when none is attached.
  if (!loop || !VpiIsWhileOrRepeatType(loop->type)) return nullptr;
  for (auto* child : loop->children) {
    if (VpiIsExprType(child->type)) return child;
  }
  return nullptr;
}

VpiHandle VpiForConditionExpr(VpiHandle for_stmt) {
  // §37.74: a for statement reaches its controlling condition through
  // vpiCondition. As with the other looping and conditional statements, the
  // condition's own type is an expression kind (an operation, a reference, a
  // constant, ...) rather than the vpiCondition relation tag, so it is found by
  // scanning for the first expression child. The body the diagram's untagged
  // arrow reaches is a statement child this scan skips, and the statements the
  // header writes are held in the for statement's own init and increment lists
  // rather than among its children. Null when no condition is attached.
  if (!for_stmt) return nullptr;
  for (auto* child : for_stmt->children) {
    if (VpiIsExprType(child->type)) return child;
  }
  return nullptr;
}

VpiHandle VpiDoWhileConditionExpr(VpiHandle do_while) {
  // §37.75: a do-while statement reaches its controlling condition through
  // vpiCondition. As with the other looping and conditional statements
  // (§37.66/§37.71/§37.74), the condition's own type is an expression kind (an
  // operation, a reference, a constant, ...) rather than the vpiCondition
  // relation tag, so it is found by scanning for the first expression child.
  // The do-while's body, drawn by the diagram's unlabeled edge to a statement,
  // is a statement-edge child that this scan skips. Null when no condition is
  // attached.
  if (!do_while) return nullptr;
  for (auto* child : do_while->children) {
    if (VpiIsExprType(child->type)) return child;
  }
  return nullptr;
}

// §37.74 (figure): the single arrows the diagram draws beside its two double
// arrows - vpiForInitStmt and vpiForIncStmt each appear twice, once as a
// one-to-one relationship reaching one statement and once as a one-to-many
// reaching every statement of that part of the header. §37.4.3 makes the single
// arrow a vpi_handle() relationship, and the statement it reaches is the first
// the header writes, the iteration walking the rest. Null where the header
// writes none, and for an object that is not a for statement.
VpiHandle VpiForHeaderStmt(int type, VpiHandle for_stmt) {
  if (!for_stmt || for_stmt->type != vpiFor) return nullptr;
  const std::vector<VpiObject*>& stmts = type == vpiForInitStmt
                                             ? for_stmt->for_init_stmts
                                             : for_stmt->for_inc_stmts;
  return stmts.empty() ? nullptr : stmts.front();
}

// §37.74 (figure): the double arrows - the initialization statements a for
// statement's header writes before the loop runs and the increment statements
// it writes after each pass, in source order. A header writes a comma list of
// either, which is why the clause draws the iteration beside the single arrow.
//
// Both were walked by looking for a child whose own type is vpiForInitStmt or
// vpiForIncStmt. Those name relations, and §37.4.1 makes the `stmt` enclosure
// they are drawn to a class grouping other objects and classes rather than a
// kind, so a statement of a design carries the kind it is and the walk reached
// the header of no for loop that could be written.
void VpiCollectForHeaderStmts(int type, VpiHandle for_stmt, VpiHandle iter) {
  const std::vector<VpiObject*>& stmts = type == vpiForInitStmt
                                             ? for_stmt->for_init_stmts
                                             : for_stmt->for_inc_stmts;
  for (auto* stmt : stmts) iter->children.push_back(stmt);
}

}  // namespace delta
