#include <vector>

#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

bool VpiIsWhileOrRepeatType(int type) {
  return type == vpiWhile || type == vpiRepeat;
}

VpiHandle VpiLoopConditionExpr(VpiHandle loop) {
  if (!loop || !VpiIsWhileOrRepeatType(loop->type)) return nullptr;
  for (auto* child : loop->children) {
    if (VpiIsOperandObject(child)) return child;
  }
  return nullptr;
}

VpiHandle VpiForConditionExpr(VpiHandle for_stmt) {
  if (!for_stmt) return nullptr;
  for (auto* child : for_stmt->children) {
    if (VpiIsOperandObject(child)) return child;
  }
  return nullptr;
}

VpiHandle VpiDoWhileConditionExpr(VpiHandle do_while) {
  if (!do_while) return nullptr;
  for (auto* child : do_while->children) {
    if (VpiIsOperandObject(child)) return child;
  }
  return nullptr;
}

VpiHandle VpiForHeaderStmt(int type, VpiHandle for_stmt) {
  if (!for_stmt || for_stmt->type != vpiFor) return nullptr;
  const std::vector<VpiObject*>& stmts = type == vpiForInitStmt
                                             ? for_stmt->for_init_stmts
                                             : for_stmt->for_inc_stmts;
  return stmts.empty() ? nullptr : stmts.front();
}

void VpiCollectForHeaderStmts(int type, VpiHandle for_stmt, VpiHandle iter) {
  const std::vector<VpiObject*>& stmts = type == vpiForInitStmt
                                             ? for_stmt->for_init_stmts
                                             : for_stmt->for_inc_stmts;
  for (auto* stmt : stmts) iter->children.push_back(stmt);
}

}  // namespace delta
