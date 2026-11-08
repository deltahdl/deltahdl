#include <cstddef>
#include <cstdio>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

bool VpiIsAssertionType(int type) {
  switch (type) {
    case vpiAssert:
    case vpiAssume:
    case vpiCover:
    case vpiRestrict:
    case vpiImmediateAssert:
    case vpiImmediateAssume:
    case vpiImmediateCover:
    case vpiSequenceInst:
    case vpiPropertyInst:
      return true;
    default:
      return false;
  }
}

bool VpiIsConstraintItemType(int type) {
  switch (type) {
    case vpiConstraintOrdering:
    case vpiImplication:
    case vpiConstrIf:
    case vpiConstrIfElse:
    case vpiConstrForEach:
    case vpiDistribution:
    case vpiSoftDisable:
      return true;
    default:
      return VpiIsExprType(type) || VpiIsVariablesType(type);
  }
}

bool VpiIsConstraintExprContainerType(int type) {
  switch (type) {
    case vpiImplication:
    case vpiConstrIf:
    case vpiConstrIfElse:
    case vpiConstrForEach:
      return true;
    default:
      return false;
  }
}

VpiHandle VpiConstraintConditionExpr(VpiHandle container) {
  if (!container) return nullptr;
  switch (container->type) {
    case vpiImplication:
    case vpiConstrIf:
    case vpiConstrIfElse:
      break;
    default:
      return nullptr;
  }
  for (auto* child : container->children) {
    if (VpiIsExprType(child->type) || VpiIsVariablesType(child->type)) {
      return child;
    }
  }
  return nullptr;
}

bool VpiIsClassMethodType(int type) {
  switch (type) {
    case vpiFunction:
    case vpiTask:
      return true;
    default:
      return false;
  }
}

bool VpiIsClassMemberValueType(int type) {
  return VpiIsVariablesType(type) || type == vpiNamedEvent ||
         type == vpiNamedEventArray;
}

VpiHandle VpiAssertionClockingBlock(VpiHandle assertion) {
  if (!assertion) return nullptr;
  for (auto* child : assertion->children) {
    if (child->type == vpiClockingBlock) return child;
  }
  return nullptr;
}

bool VpiIsConcurrentAssertionType(int type) {
  switch (type) {
    case vpiAssert:
    case vpiAssume:
    case vpiCover:
    case vpiRestrict:
      return true;
    default:
      return false;
  }
}

bool VpiIsConcurrentAssertionPropertyType(int type) {
  return type == vpiPropertyInst || type == vpiPropertySpec;
}

VpiHandle VpiConcurrentAssertionProperty(VpiHandle assertion) {
  if (!assertion) return nullptr;
  for (auto* child : assertion->children) {
    if (VpiIsConcurrentAssertionPropertyType(child->type)) return child;
  }
  return nullptr;
}

VpiHandle VpiConcurrentAssertionClockingEvent(VpiHandle assertion) {
  return assertion != nullptr ? assertion->clocking_event : nullptr;
}

bool VpiConcurrentAssertionHasPassStmt(int type) {
  switch (type) {
    case vpiAssert:
    case vpiAssume:
    case vpiCover:
      return true;
    default:
      return false;
  }
}

bool VpiConcurrentAssertionHasElseStmt(int type) {
  return type == vpiAssert || type == vpiAssume;
}

static std::vector<VpiHandle> ActionStmts(VpiHandle assertion) {
  std::vector<VpiHandle> stmts;
  for (auto* child : assertion->children) {
    if (VpiIsScopeBodyStmtObject(child)) stmts.push_back(child);
  }
  return stmts;
}

static VpiHandle PassAction(VpiHandle assertion) {
  std::vector<VpiHandle> stmts = ActionStmts(assertion);
  std::erase(stmts, assertion->else_stmt);
  return stmts.empty() ? nullptr : stmts.front();
}

static VpiHandle ElseAction(VpiHandle assertion) {
  if (assertion->else_stmt != nullptr) return assertion->else_stmt;
  std::vector<VpiHandle> stmts = ActionStmts(assertion);
  return stmts.size() < 2 ? nullptr : stmts[1];
}

VpiHandle VpiConcurrentAssertionStmt(VpiHandle assertion) {
  if (!assertion || !VpiConcurrentAssertionHasPassStmt(assertion->type)) {
    return nullptr;
  }
  return PassAction(assertion);
}

VpiHandle VpiConcurrentAssertionElseStmt(VpiHandle assertion) {
  if (!assertion || !VpiConcurrentAssertionHasElseStmt(assertion->type)) {
    return nullptr;
  }
  return ElseAction(assertion);
}

bool VpiConcurrentAssertionIsSimulated(int type) {
  return VpiIsConcurrentAssertionType(type) && type != vpiRestrict;
}

bool VpiIsImmediateAssertionType(int type) {
  switch (type) {
    case vpiImmediateAssert:
    case vpiImmediateAssume:
    case vpiImmediateCover:
      return true;
    default:
      return false;
  }
}

bool VpiImmediateAssertionHasElseStmt(int type) {
  return type == vpiImmediateAssert || type == vpiImmediateAssume;
}

VpiHandle VpiImmediateAssertionExpr(VpiHandle assertion) {
  if (!assertion) return nullptr;
  for (auto* child : assertion->children) {
    if (VpiIsOperandObject(child)) return child;
  }
  return nullptr;
}

VpiHandle VpiImmediateAssertionStmt(VpiHandle assertion) {
  return assertion != nullptr ? PassAction(assertion) : nullptr;
}

VpiHandle VpiImmediateAssertionElseStmt(VpiHandle assertion) {
  if (!assertion) return nullptr;
  if (!VpiImmediateAssertionHasElseStmt(assertion->type)) return nullptr;
  return ElseAction(assertion);
}

bool VpiIsSequenceExprType(int type) {
  switch (type) {
    case vpiOperation:
    case vpiSequenceInst:
    case vpiDistribution:
    case vpiConstant:
    case vpiRefObj:
      return true;
    default:
      return false;
  }
}

bool VpiIsSequenceExprOpType(int op) {
  switch (op) {
    case vpiCompAndOp:
    case vpiIntersectOp:
    case vpiCompOrOp:
    case vpiFirstMatchOp:
    case vpiThroughoutOp:
    case vpiWithinOp:
    case vpiUnaryCycleDelayOp:
    case vpiCycleDelayOp:
    case vpiRepeatOp:
    case vpiConsecutiveRepeatOp:
    case vpiGotoRepeatOp:
      return true;
    default:
      return false;
  }
}

static bool VpiRangeUpperDiffers(VpiHandle lower, VpiHandle upper) {
  return upper != nullptr && upper != lower;
}

std::vector<VpiHandle> VpiUnaryCycleDelayOperands(VpiHandle sequence,
                                                  VpiHandle left_range,
                                                  VpiHandle right_range) {
  std::vector<VpiHandle> operands = {sequence, left_range};
  if (VpiRangeUpperDiffers(left_range, right_range)) {
    operands.push_back(right_range);
  }
  return operands;
}

std::vector<VpiHandle> VpiCycleDelayOperands(VpiHandle lhs_sequence,
                                             VpiHandle rhs_sequence,
                                             VpiHandle left_range,
                                             VpiHandle right_range) {
  std::vector<VpiHandle> operands = {lhs_sequence, rhs_sequence, left_range};
  if (VpiRangeUpperDiffers(left_range, right_range)) {
    operands.push_back(right_range);
  }
  return operands;
}

std::vector<VpiHandle> VpiRepeatOperands(VpiHandle sequence,
                                         VpiHandle left_bound,
                                         VpiHandle right_bound) {
  std::vector<VpiHandle> operands = {sequence, left_bound};
  if (VpiRangeUpperDiffers(left_bound, right_bound)) {
    operands.push_back(right_bound);
  }
  return operands;
}

std::vector<VpiHandle> VpiSequenceInstArguments(
    const std::vector<VpiSequenceFormal>& formals,
    const std::vector<VpiHandle>& provided) {
  std::vector<VpiHandle> arguments;
  arguments.reserve(formals.size());
  for (size_t i = 0; i < formals.size(); ++i) {
    VpiHandle actual = i < provided.size() ? provided[i] : nullptr;
    arguments.push_back(actual != nullptr ? actual : formals[i].default_value);
  }
  return arguments;
}

bool VpiIsSequenceArgumentType(int type) {
  return type == vpiNamedEvent || VpiIsSequenceExprType(type);
}

VpiHandle VpiSequenceInstDecl(VpiHandle sequence_inst) {
  return sequence_inst == nullptr ? nullptr : sequence_inst->sequence_decl;
}

bool VpiIsMatchItemType(int type) {
  switch (type) {
    case vpiAssignment:
    case vpiFuncCall:
    case vpiTaskCall:
      return true;
    default:
      return false;
  }
}

std::vector<VpiHandle> VpiExprMatchItems(VpiHandle expr) {
  std::vector<VpiHandle> items;
  if (!expr) return items;
  for (auto* child : expr->children) {
    if (VpiIsMatchItemType(child->type)) items.push_back(child);
  }
  return items;
}

bool VpiIsPropertyExprType(int type) {
  switch (type) {
    case vpiOperation:
    case vpiMulticlockSequenceExpr:
    case vpiPropertyInst:
    case vpiClockedProp:
    case vpiCaseProperty:
      return true;
    default:
      return false;
  }
}

bool VpiIsPropertyExprOpType(int op) {
  switch (op) {
    case vpiAcceptOnOp:
    case vpiAlwaysOp:
    case vpiCompAndOp:
    case vpiCompOrOp:
    case vpiEventuallyOp:
    case vpiIfElseOp:
    case vpiIfOp:
    case vpiIffOp:
    case vpiImpliesOp:
    case vpiNexttimeOp:
    case vpiNonOverlapFollowedByOp:
    case vpiNonOverlapImplyOp:
    case vpiNotOp:
    case vpiOverlapFollowedByOp:
    case vpiOverlapImplyOp:
    case vpiRejectOnOp:
    case vpiSyncAcceptOnOp:
    case vpiSyncRejectOnOp:
    case vpiUntilOp:
    case vpiUntilWithOp:
      return true;
    default:
      return false;
  }
}

std::vector<VpiHandle> VpiNexttimeOperands(VpiHandle property,
                                           VpiHandle constant,
                                           bool constant_differs_from_one) {
  std::vector<VpiHandle> operands = {property};
  if (constant != nullptr && constant_differs_from_one) {
    operands.push_back(constant);
  }
  return operands;
}

std::vector<VpiHandle> VpiAlwaysEventuallyOperands(VpiHandle property,
                                                   VpiHandle left_range,
                                                   VpiHandle right_range) {
  std::vector<VpiHandle> operands = {property};
  if (left_range != nullptr) operands.push_back(left_range);
  if (right_range != nullptr) operands.push_back(right_range);
  return operands;
}

bool VpiIsOpStrongValidOp(int op) {
  switch (op) {
    case vpiNexttimeOp:
    case vpiAlwaysOp:
    case vpiEventuallyOp:
    case vpiUntilOp:
    case vpiUntilWithOp:
      return true;
    default:
      return false;
  }
}

bool VpiIsPropertyVariableValueAccessible() { return false; }

std::vector<VpiHandle> VpiCaseItemConditions(VpiHandle case_item) {
  if (!case_item) return {};
  return case_item->children;
}

VpiHandle VpiCasePropertyConditionExpr(VpiHandle case_property) {
  if (!case_property) return nullptr;
  for (auto* child : case_property->children) {
    if (child->type == vpiCasePropertyItem) continue;
    if (VpiIsExprType(child->type) || child->type == vpiExpr ||
        VpiIsOperandObject(child)) {
      return child;
    }
  }
  return nullptr;
}

bool VpiIsDisableConditionType(int type) {
  switch (type) {
    case vpiDistribution:
    case vpiExpr:
    case vpiOperation:
    case vpiConstant:
    case vpiRefObj:
      return true;
    default:
      return false;
  }
}

VpiHandle VpiClockingEvent(VpiHandle obj) {
  if (!obj) return nullptr;
  if (obj->clocking_event != nullptr) return obj->clocking_event;
  for (auto* child : obj->children) {
    if (child->type == vpiEventControl) return child;
  }
  return nullptr;
}

VpiHandle VpiPropertyExprChild(VpiHandle obj) {
  if (!obj) return nullptr;
  for (auto* child : obj->children) {
    if (VpiIsPropertyExprType(child->type)) return child;
  }
  return nullptr;
}

std::vector<VpiHandle> VpiPropFormals(VpiHandle property_decl) {
  std::vector<VpiHandle> formals;
  if (!property_decl) return formals;
  for (auto* child : property_decl->children) {
    if (child->type == vpiPropFormalDecl) formals.push_back(child);
  }
  return formals;
}

int VpiPropFormalDirection(bool is_local_variable_argument) {
  return is_local_variable_argument ? vpiInput : vpiNoDirection;
}

VpiHandle VpiPropFormalTypespec(VpiHandle formal) {
  if (!formal) return nullptr;
  for (auto* child : formal->children) {
    if (child->type == vpiTypespec) return child;
  }
  return nullptr;
}

VpiHandle VpiPropFormalInitExpr(VpiHandle formal) {
  if (!formal) return nullptr;
  for (auto* child : formal->children) {
    if (child->type == vpiNamedEvent || VpiIsPropertyExprType(child->type) ||
        VpiIsOperandObject(child)) {
      return child;
    }
  }
  return nullptr;
}

std::vector<VpiHandle> VpiPropertyInstArguments(
    const std::vector<VpiPropertyFormal>& formals,
    const std::vector<VpiHandle>& provided) {
  std::vector<VpiHandle> arguments;
  arguments.reserve(formals.size());
  for (size_t i = 0; i < formals.size(); ++i) {
    VpiHandle actual = i < provided.size() ? provided[i] : nullptr;
    arguments.push_back(actual != nullptr ? actual : formals[i].default_value);
  }
  return arguments;
}

bool VpiIsPropertyArgumentType(int type) {
  return type == vpiNamedEvent || VpiIsPropertyExprType(type);
}

VpiHandle VpiPropertyInstDecl(VpiHandle property_inst) {
  return property_inst == nullptr ? nullptr : property_inst->property_decl;
}

std::vector<VpiHandle> VpiMulticlockSequenceClockedSeqs(
    VpiHandle multiclock_seq) {
  std::vector<VpiHandle> clocked_seqs;
  if (!multiclock_seq) return clocked_seqs;
  for (auto* child : multiclock_seq->children) {
    if (child->type == vpiClockedSeq) clocked_seqs.push_back(child);
  }
  return clocked_seqs;
}

VpiHandle VpiClockedSeqSequenceExpr(VpiHandle clocked_seq) {
  if (!clocked_seq) return nullptr;
  for (auto* child : clocked_seq->children) {
    if (VpiIsSequenceExprType(child->type)) return child;
  }
  return nullptr;
}

std::vector<VpiHandle> VpiSeqFormals(VpiHandle sequence_decl) {
  std::vector<VpiHandle> formals;
  if (!sequence_decl) return formals;
  for (auto* child : sequence_decl->children) {
    if (child->type == vpiSeqFormalDecl) formals.push_back(child);
  }
  return formals;
}

VpiHandle VpiSeqDeclBodyExpr(VpiHandle sequence_decl) {
  return sequence_decl == nullptr ? nullptr : sequence_decl->body;
}

int VpiSeqFormalDirection(bool is_local_variable_argument,
                          int local_direction) {
  return is_local_variable_argument ? local_direction : vpiNoDirection;
}

VpiHandle VpiSeqFormalTypespec(VpiHandle formal) {
  if (!formal) return nullptr;
  for (auto* child : formal->children) {
    if (child->type == vpiTypespec) return child;
  }
  return nullptr;
}

VpiHandle VpiSeqFormalInitExpr(VpiHandle formal) {
  if (!formal) return nullptr;
  for (auto* child : formal->children) {
    if (child->type == vpiNamedEvent || VpiIsSequenceExprType(child->type) ||
        VpiIsOperandObject(child)) {
      return child;
    }
  }
  return nullptr;
}

VpiHandle VpiLetFormalDefault(VpiHandle formal) {
  if (!formal) return nullptr;
  for (auto* child : formal->children) {
    if (VpiIsExprType(child->type)) return child;
  }
  return nullptr;
}

std::vector<VpiHandle> VpiLetExprArguments(
    const std::vector<VpiLetFormal>& formals,
    const std::vector<VpiHandle>& provided) {
  std::vector<VpiHandle> arguments;
  arguments.reserve(formals.size());
  for (size_t i = 0; i < formals.size(); ++i) {
    VpiHandle actual = i < provided.size() ? provided[i] : nullptr;
    arguments.push_back(actual != nullptr ? actual : formals[i].default_value);
  }
  return arguments;
}

bool VpiSimpleExprVectorUseAccessesUse(bool references_vector,
                                       bool references_part_select_of_vector,
                                       bool references_bit_select_of_vector) {
  return references_vector || references_part_select_of_vector ||
         references_bit_select_of_vector;
}

bool VpiSimpleExprBitSelectUseAccessesUse(
    bool references_this_bit, bool references_parent_vector,
    bool references_part_select_containing_bit) {
  return references_this_bit || references_parent_vector ||
         references_part_select_containing_bit;
}

bool VpiSimpleExprBitSelectConstantSelect(bool all_indices_constant,
                                          bool parent_constant_select) {
  return all_indices_constant && parent_constant_select;
}

bool VpiBitSelectConstantSelectOf(VpiHandle select) {
  if (!select || select->type != vpiBitSelect) return false;

  bool all_indices_constant = select->index_expr == nullptr ||
                              VpiIsElaborationConstant(select->index_expr);
  for (const VpiObject* child : select->children) {
    if (!VpiIsExprType(child->type)) continue;
    if (!VpiIsElaborationConstant(child)) all_indices_constant = false;
  }

  VpiHandle parent = select->parent;
  bool parent_constant_select = false;
  if (parent != nullptr) {
    if (parent->type == vpiBitSelect) {
      parent_constant_select = VpiBitSelectConstantSelectOf(parent);
    } else if (parent->type == vpiVarSelect) {
      parent_constant_select = VpiVarSelectConstantSelectOf(parent);
    } else {
      parent_constant_select = !parent->automatic;
    }
  }

  return VpiSimpleExprBitSelectConstantSelect(all_indices_constant,
                                              parent_constant_select);
}

bool VpiIsDynamicPrefixSourceType(int type) {
  if (VpiIsNetsType(type) || VpiIsVariablesType(type)) return true;
  switch (type) {
    case vpiRefObj:
    case vpiParameter:
    case vpiSpecParam:
    case vpiVarSelect:
    case vpiBitSelect:
    case vpiPartSelect:
    case vpiIndexedPartSelect:
    case vpiNamedEvent:
    case vpiNamedEventArray:
      return true;
    default:
      return false;
  }
}

bool VpiObjectHasActual(int actual_origin, bool has_current_actual) {
  switch (actual_origin) {
    case kVpiActualStaticElab:
    case kVpiActualFrameVar:
      return true;
    case kVpiActualLexicalDefn:
    case kVpiActualClassTypespec:
    case kVpiActualTaskFuncVar:
      return false;
    case kVpiActualBySimTime:
    default:
      return has_current_actual;
  }
}

void VpiCollectConstraintExprs(VpiObject* ref, VpiObject* iter) {
  for (auto* expr : ref->constraint_exprs) {
    iter->children.push_back(expr);
  }
}

}  // namespace delta
