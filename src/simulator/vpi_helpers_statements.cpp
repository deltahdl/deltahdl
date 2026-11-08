#include <cctype>
#include <cstddef>
#include <cstdio>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

bool VpiIsExprType(int type) {
  switch (type) {
    case vpiOperation:
    case vpiConstant:
    case vpiPartSelect:
    case vpiIndexedPartSelect:
    case vpiFuncCall:
    case vpiMethodFuncCall:
    case vpiSysFuncCall:
    case vpiLetExpr:
    case vpiRefObj:
    case vpiParameter:
    case vpiSpecParam:
    case vpiVarSelect:
    case vpiBitSelect:
      return true;
    default:
      return false;
  }
}

bool VpiIsAtomicStmtType(int type) {
  if (VpiIsWaitType(type) || VpiIsDisableType(type)) return true;
  switch (type) {
    case vpiIf:
    case vpiIfElse:
    case vpiWhile:
    case vpiRepeat:
    case vpiCase:
    case vpiFor:
    case vpiDelayControl:
    case vpiEventControl:
    case vpiEventStmt:
    case vpiAssignment:
    case vpiAssignStmt:
    case vpiDeassign:
    case vpiTaskCall:
    case vpiSysTaskCall:
    case vpiMethodTaskCall:
    case vpiForever:
    case vpiForce:
    case vpiRelease:
    case vpiDoWhile:
    case vpiExpectStmt:
    case vpiForeachStmt:
    case vpiImmediateAssert:
    case vpiImmediateAssume:
    case vpiImmediateCover:
    case vpiReturnStmt:
    case vpiBreak:
    case vpiContinue:
    case vpiNullStmt:
      return true;
    default:
      return false;
  }
}

bool VpiIsAtomicStmtObject(VpiHandle obj) {
  if (VpiIsAtomicStmtType(obj->type)) return true;
  const bool kFunctionCall = obj->type == vpiFuncCall ||
                             obj->type == vpiMethodFuncCall ||
                             obj->type == vpiSysFuncCall;
  return kFunctionCall && obj->written_as_stmt;
}

bool VpiIsScopeBodyStmtObject(VpiHandle obj) {
  return VpiIsAtomicStmtObject(obj) || VpiIsScopeBodyStmtType(obj->type);
}

bool VpiIsPatternType(int type) {
  switch (type) {
    case vpiAnyPattern:
    case vpiTaggedPattern:
    case vpiStructPattern:
      return true;
    default:
      return false;
  }
}

VpiHandle VpiPatternOf(VpiHandle pattern) {
  if (!pattern) return nullptr;
  for (auto* child : pattern->children) {
    if (VpiIsPatternType(child->type) || VpiIsExprOperandType(child->type)) {
      return child;
    }
  }
  return nullptr;
}

bool VpiIsCaseItemConditionType(int type) {
  if (VpiIsPatternType(type)) return true;
  return type == vpiExpr || VpiIsExprType(type);
}

VpiHandle VpiCaseConditionExpr(VpiHandle case_stmt) {
  if (!case_stmt) return nullptr;
  for (auto* child : case_stmt->children) {
    if (VpiIsOperandObject(child)) return child;
  }
  return nullptr;
}

std::vector<VpiHandle> VpiCaseItemMatchExprs(VpiHandle case_item) {
  std::vector<VpiHandle> conditions;
  if (!case_item || case_item->default_case_item) return conditions;
  for (auto* child : case_item->children) {
    if (VpiIsCaseItemConditionType(child->type) && !child->written_as_stmt) {
      conditions.push_back(child);
    }
  }
  return conditions;
}

int VpiAssignmentOpType(std::string_view assign_operator) {
  if (assign_operator == "+=") return vpiAddOp;
  if (assign_operator == "-=") return vpiSubOp;
  if (assign_operator == "*=") return vpiMultOp;
  if (assign_operator == "/=") return vpiDivOp;
  if (assign_operator == "%=") return vpiModOp;
  if (assign_operator == "&=") return vpiBitAndOp;
  if (assign_operator == "|=") return vpiBitOrOp;
  if (assign_operator == "^=") return vpiBitXorOp;
  if (assign_operator == "<<=") return vpiLShiftOp;
  if (assign_operator == ">>=") return vpiRShiftOp;
  if (assign_operator == "<<<=") return vpiArithLShiftOp;
  if (assign_operator == ">>>=") return vpiArithRShiftOp;
  return vpiAssignmentOp;
}

std::vector<VpiHandle> VpiOperationOperands(VpiHandle operation) {
  std::vector<VpiHandle> operands;
  if (!operation || operation->type != vpiOperation) return operands;
  for (auto* child : operation->children) {
    if (VpiIsExprOperandType(child->type) ||
        VpiIsPropertyExprType(child->type) ||
        VpiIsSequenceExprType(child->type) || VpiIsPatternType(child->type)) {
      operands.push_back(child);
    }
  }
  return operands;
}

bool VpiIsProcessType(int type) {
  return type == vpiAlways || type == vpiInitial || type == vpiFinal;
}

bool VpiIsAlwaysType(int always_type) {
  return always_type == vpiAlways || always_type == vpiAlwaysComb ||
         always_type == vpiAlwaysFF || always_type == vpiAlwaysLatch;
}

bool VpiIsBodyStmtOwnerType(int type) {
  return VpiIsProcessType(type) || VpiIsWhileOrRepeatType(type) ||
         VpiIsWaitType(type) || type == vpiForever ||
         VpiIsIfOrIfElseType(type) || type == vpiExpectStmt || type == vpiFor ||
         type == vpiDoWhile || type == vpiForeachStmt || type == vpiCaseItem;
}

bool VpiIsWaitType(int type) {
  return type == vpiWait || type == vpiOrderedWait || type == vpiWaitFork;
}

VpiHandle VpiWaitConditionExpr(VpiHandle wait) {
  if (!wait) return nullptr;
  for (auto* child : wait->children) {
    if (VpiIsOperandObject(child) || child->type == vpiSequenceInst) {
      return child;
    }
  }
  return nullptr;
}

bool VpiIsContAssignKind(int type) {
  return type == vpiContAssign || type == vpiContAssignBit;
}

namespace {

VpiHandle SecondBodyStmt(VpiHandle stmt) {
  if (stmt->else_stmt != nullptr) return stmt->else_stmt;
  int seen = 0;
  for (auto* child : stmt->children) {
    if (!VpiIsScopeBodyStmtObject(child)) continue;
    if (++seen == 2) return child;
  }
  return nullptr;
}

}  // namespace

VpiHandle VpiOrderedWaitElseStmt(VpiHandle wait) {
  if (!wait || wait->type != vpiOrderedWait) return nullptr;
  return SecondBodyStmt(wait);
}

VpiHandle VpiExpectElseStmt(VpiHandle expect) {
  if (!expect || expect->type != vpiExpectStmt) return nullptr;
  return SecondBodyStmt(expect);
}

bool VpiIsDisableType(int type) {
  return type == vpiDisable || type == vpiDisableFork;
}

bool VpiIsDisableTargetType(int type) {
  switch (type) {
    case vpiTask:
    case vpiFunction:
    case vpiNamedBegin:
    case vpiNamedFork:
      return true;
    default:
      return false;
  }
}

VpiHandle VpiDisableExpr(VpiHandle disable) {
  if (!disable) return nullptr;
  if (disable->disable_target != nullptr) return disable->disable_target;
  for (auto* child : disable->children) {
    if (VpiIsDisableTargetType(child->type)) return child;
  }
  return nullptr;
}

bool VpiIsIfOrIfElseType(int type) {
  return type == vpiIf || type == vpiIfElse;
}

VpiHandle VpiIfConditionExpr(VpiHandle if_stmt) {
  if (!if_stmt) return nullptr;
  for (auto* child : if_stmt->children) {
    if (VpiIsOperandObject(child)) return child;
  }
  return nullptr;
}

VpiHandle VpiIfElseStmt(VpiHandle if_stmt) {
  if (!if_stmt) return nullptr;
  return SecondBodyStmt(if_stmt);
}

VpiHandle VpiReturnConditionExpr(VpiHandle return_stmt) {
  if (!return_stmt) return nullptr;
  for (auto* child : return_stmt->children) {
    if (VpiIsExprType(child->type)) return child;
  }
  return nullptr;
}

bool VpiIsBlockItemDeclType(int type) {
  switch (type) {
    case vpiLogicVar:
    case vpiIntegerVar:
    case vpiRealVar:
    case vpiShortRealVar:
    case vpiTimeVar:
    case vpiByteVar:
    case vpiShortIntVar:
    case vpiIntVar:
    case vpiLongIntVar:
    case vpiBitVar:
    case vpiEnumVar:
    case vpiStructVar:
    case vpiUnionVar:
    case vpiStringVar:
    case vpiClassVar:
    case vpiChandleVar:
    case vpiPackedArrayVar:
    case vpiArrayVar:
    case vpiTypedef:
    case vpiParameter:
      return true;
    default:
      return false;
  }
}

bool VpiBlockScopeIsScope(VpiHandle block) {
  if (!block) return false;
  switch (block->type) {
    case vpiNamedBegin:
    case vpiNamedFork:
      return true;
    case vpiBegin:
    case vpiFork:
      for (auto* child : block->children) {
        if (VpiIsBlockItemDeclType(child->type)) return true;
      }
      return false;
    case vpiFor:
      return block->local_var_decls;
    default:
      return false;
  }
}

bool VpiIsLoopControlVarType(int type) {
  return VpiIsBlockItemDeclType(type) && type != vpiTypedef &&
         type != vpiParameter;
}

bool VpiIsVirtualInterfaceArray(VpiHandle obj) {
  if (!obj || !VpiIsArrayVarType(obj->type)) return false;
  for (auto* elem : obj->children) {
    if (elem->type == vpiVirtualInterfaceVar) return true;
  }
  return false;
}

bool VpiIsJoinType(int join_type) {
  return join_type == vpiJoin || join_type == vpiJoinNone ||
         join_type == vpiJoinAny;
}

bool VpiIsTaskFuncType(int type) {
  return type == vpiTask || type == vpiFunction || type == vpiTaskFunc;
}

bool VpiIsScopeBodyStmtType(int type) {
  if (VpiIsAtomicStmtType(type)) return true;
  switch (type) {
    case vpiBegin:
    case vpiNamedBegin:
    case vpiFork:
    case vpiNamedFork:
      return true;
    default:
      return false;
  }
}

VpiHandle VpiTaskFuncStmt(VpiHandle task_func) {
  if (!task_func) return nullptr;
  for (auto* child : task_func->children) {
    if (VpiIsScopeBodyStmtObject(child)) return child;
  }
  return nullptr;
}

std::vector<VpiHandle> VpiMultiConcatOperands(
    VpiHandle multiplier, const std::vector<VpiHandle>& concat_exprs) {
  std::vector<VpiHandle> operands;
  operands.reserve(concat_exprs.size() + 1);
  operands.push_back(multiplier);
  operands.insert(operands.end(), concat_exprs.begin(), concat_exprs.end());
  return operands;
}

std::vector<VpiHandle> VpiMultiAssignmentPatternOperands(
    VpiHandle multiplier, const std::vector<VpiHandle>& pattern_exprs) {
  std::vector<VpiHandle> operands;
  operands.reserve(pattern_exprs.size() + 1);
  operands.push_back(multiplier);
  operands.insert(operands.end(), pattern_exprs.begin(), pattern_exprs.end());
  return operands;
}

std::vector<VpiHandle> VpiCastOpOperands(VpiHandle cast_expr) {
  return {cast_expr};
}

std::vector<VpiHandle> VpiAssignmentPatternPositionalOperands(
    int slots, const std::vector<VpiAssignmentPatternEntry>& positioned,
    VpiHandle default_value) {
  size_t count = slots > 0 ? static_cast<size_t>(slots) : 0;
  std::vector<VpiHandle> operands(count, default_value);
  for (const auto& entry : positioned) {
    if (entry.position >= 0 && entry.position < slots) {
      operands[static_cast<size_t>(entry.position)] = entry.value;
    }
  }
  return operands;
}

bool VpiTypespecAlwaysAvailable(int op_type, bool is_simple_expr,
                                bool assignment_pattern_has_type_prefix) {
  if (is_simple_expr) return true;
  if (op_type == vpiCastOp) return true;
  if (op_type == vpiAssignmentPatternOp ||
      op_type == vpiMultiAssignmentPatternOp) {
    return assignment_pattern_has_type_prefix;
  }
  return false;
}

bool VpiPartSelectConstantSelect(
    const VpiPartSelectConstantSelectQuery& query) {
  return query.parent_constant_select && query.parent_array_has_static_bounds &&
         query.all_range_exprs_constant;
}

std::string VpiPartSelectParentExpr(std::string_view select_expr) {
  size_t end = select_expr.size();
  while (end > 0 &&
         std::isspace(static_cast<unsigned char>(select_expr[end - 1]))) {
    --end;
  }
  if (end == 0 || select_expr[end - 1] != ']') {
    return std::string(select_expr.substr(0, end));
  }
  int depth = 0;
  size_t i = end;
  while (i > 0) {
    --i;
    char c = select_expr[i];
    if (c == ']') {
      ++depth;
    } else if (c == '[') {
      --depth;
      if (depth == 0) break;
    }
  }
  return std::string(select_expr.substr(0, i));
}

std::string VpiDecompileJoin(const std::vector<std::string>& pieces) {
  std::string out;
  for (const auto& piece : pieces) {
    if (piece.empty()) continue;
    if (!out.empty()) out.push_back(' ');
    out += piece;
  }
  return out;
}

std::string VpiDecompileParenthesize(std::string_view inner) {
  std::string out = "(";
  out += inner;
  out.push_back(')');
  return out;
}

bool VpiIsTfCallType(int type) {
  switch (type) {
    case vpiFuncCall:
    case vpiTaskCall:
    case vpiMethodFuncCall:
    case vpiMethodTaskCall:
    case vpiSysFuncCall:
    case vpiSysTaskCall:
      return true;
    default:
      return false;
  }
}

const std::vector<VpiObject*>& VpiSubexpressions(const VpiObject& expr) {
  return VpiIsTfCallType(expr.type) ? expr.arguments : expr.children;
}

bool VpiIsMethodCallType(int type) {
  return type == vpiMethodFuncCall || type == vpiMethodTaskCall;
}

bool VpiIsTfCallArgumentType(int type) {
  if (VpiIsExprOperandType(type) || VpiIsInterfaceExprType(type) ||
      VpiIsInternalScopeType(type)) {
    return true;
  }
  switch (type) {
    case vpiNamedEvent:
    case vpiNamedEventArray:
      return true;
    default:
      return VpiObjectIsPrimitive(type);
  }
}

void VpiMakeEmptyArgument(VpiHandle arg) {
  if (!arg) return;
  arg->type = vpiOperation;
  arg->op_type = vpiNullOp;
}

void VpiMakeNullArgument(VpiHandle arg) {
  if (!arg) return;
  arg->type = vpiConstant;
  arg->const_type = vpiNullConst;
}

void VpiCollectTfCallArguments(VpiHandle call, VpiHandle iter) {
  for (VpiObject* arg : call->arguments) {
    if (arg != nullptr && VpiIsTfCallArgumentType(arg->type)) {
      iter->children.push_back(arg);
    }
  }
}

VpiHandle VpiFrameParent(VpiHandle frame) {
  if (!frame || !frame->parent) return nullptr;
  return frame->parent->type == vpiFrame ? frame->parent : nullptr;
}

VpiHandle VpiFrameOrigin(VpiHandle frame) {
  return frame != nullptr ? frame->frame_facts.origin : nullptr;
}

VpiHandle VpiFrameStmt(VpiHandle frame) {
  return frame != nullptr ? frame->frame_facts.stmt : nullptr;
}

VpiHandle VpiFrameThread(VpiHandle frame) {
  if (!frame) return nullptr;
  VpiHandle up = frame;
  while (up->parent != nullptr && up->parent->type == vpiFrame) {
    up = up->parent;
  }
  if (up->parent != nullptr && up->parent->type == vpiThread) return up->parent;
  return nullptr;
}

std::vector<VpiHandle> VpiFrameAutomatics(VpiHandle frame) {
  std::vector<VpiHandle> automatics;
  VpiHandle origin = VpiFrameOrigin(frame);
  if (origin == nullptr || origin->tf_decl == nullptr) return automatics;
  for (auto* child : origin->tf_decl->children) {
    const bool kDeclared = VpiIsVariablesType(child->type) ||
                           child->type == vpiNamedEvent ||
                           child->type == vpiNamedEventArray;
    if (kDeclared && child->automatic) automatics.push_back(child);
  }
  return automatics;
}

}  // namespace delta
