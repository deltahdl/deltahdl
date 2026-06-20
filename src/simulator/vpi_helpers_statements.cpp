#include "simulator/vpi.h"

#include <algorithm>
#include <cctype>
#include <cmath>
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/dpi.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
// §37.10 detail 3: the package/interface/program instance kinds are defined in
// the SystemVerilog VPI header alongside the §37.10 vpiInstance relation.
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"

#include "simulator/vpi_internal.h"

namespace delta {

bool VpiIsExprType(int type) {
  // §37.59: the member kinds the expr class draws - an operation, a constant, a
  // part-select or indexed part-select, the func/method-func/sys-func calls, a
  // let expression, and a reference (the concrete simple expression). Variables
  // and nets are not expressions, so a protected variable still has its
  // properties guarded (detail 8 carves out only protected expressions).
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
      return true;
    default:
      return false;
  }
}

bool VpiIsAtomicStmtType(int type) {
  // §37.60: the members drawn inside the atomic stmt class. The waits,
  // disables, and tf call entries are themselves groupings; their concrete
  // kinds (the wait, the disable, and the task/system-task calls) stand in for
  // them here.
  switch (type) {
    case vpiIf:
    case vpiIfElse:
    case vpiWhile:
    case vpiRepeat:
    case vpiWait:  // the "waits" grouping
    case vpiCase:
    case vpiFor:
    case vpiDelayControl:
    case vpiEventControl:
    case vpiEventStmt:
    case vpiAssignment:
    case vpiAssignStmt:
    case vpiDeassign:
    case vpiDisable:      // the "disables" grouping
    case vpiTaskCall:     // the "tf call" grouping: a task call ...
    case vpiSysTaskCall:  // ... or a system-task call
    case vpiForever:
    case vpiForce:
    case vpiRelease:
    case vpiDoWhile:
    case vpiExpectStmt:
    case vpiForeachStmt:
    case vpiImmediateAssert:
    // vpiReturn shares this constant value with vpiImmediateAssume in this
    // header set, so the return statement is classified through the same case.
    case vpiImmediateAssume:
    case vpiImmediateCover:
    case vpiBreak:
    case vpiContinue:
    case vpiNullStmt:
      return true;
    default:
      return false;
  }
}

bool VpiIsCaseItemConditionType(int type) {
  // §37.72: a case item reaches its match expressions through the vpiExpr edge,
  // which the diagram draws to both the pattern grouping and a plain expr. A
  // condition is therefore one of the pattern kinds (any/tagged/struct pattern,
  // or a bare pattern) or an expression.
  switch (type) {
    case vpiAnyPattern:
    case vpiTaggedPattern:
    case vpiStructPattern:
    case vpiPattern:
    case vpiExpr:
      return true;
    default:
      return VpiIsExprType(type);
  }
}

std::vector<VpiHandle> VpiCaseItemMatchExprs(VpiHandle case_item) {
  // §37.72 detail 1: a case item groups every case condition that branches to
  // the same statement; those conditions are its match-expression members. The
  // statement reached through the item's -> stmt edge is not one of them, so
  // only the pattern/expr children are collected, in declaration order. The
  // default case item has no condition expression (detail 2), so it groups none
  // - enforced here even if the object carries stray children.
  std::vector<VpiHandle> conditions;
  if (!case_item || case_item->default_case_item) return conditions;
  for (auto* child : case_item->children) {
    if (VpiIsCaseItemConditionType(child->type)) conditions.push_back(child);
  }
  return conditions;
}

int VpiAssignmentOpType(std::string_view assign_operator) {
  // §37.64 detail 1: an assignment operator reports the operator combined with
  // the assignment, per 11.4.1. The plain "=" and "<=" forms are normal
  // assignments and report vpiAssignmentOp, as does any spelling that is not an
  // assignment operator.
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

bool VpiIsAlwaysType(int always_type) {
  // §37.63 detail 1: vpiAlwaysType can be exactly one of these four constants.
  // vpiAlways names a general always procedure; vpiAlwaysComb, vpiAlwaysFF, and
  // vpiAlwaysLatch name the three specialized
  // always_comb/always_ff/always_latch forms. Nothing else is an always type.
  return always_type == vpiAlways || always_type == vpiAlwaysComb ||
         always_type == vpiAlwaysFF || always_type == vpiAlwaysLatch;
}

VpiHandle VpiEventControlStmt(VpiHandle event_control) {
  // §37.65 detail 1: an event control reaches the statement it guards through
  // vpiStmt. When the event control is associated with an assignment - i.e. it
  // is the event control drawn on an assignment object (§37.64) - that
  // statement is always null, since the assignment itself is the action and
  // there is no separate guarded statement. For any other event control the
  // first statement child is returned, or null when none is attached.
  if (!event_control) return nullptr;
  if (event_control->parent && event_control->parent->type == vpiAssignment) {
    return nullptr;
  }
  for (auto* child : event_control->children) {
    if (child->type == vpiStmt) return child;
  }
  return nullptr;
}

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
  if (!loop) return nullptr;
  for (auto* child : loop->children) {
    if (VpiIsExprType(child->type)) return child;
  }
  return nullptr;
}

bool VpiIsWaitType(int type) {
  // §37.67: the wait statements the diagram groups under the abstract "waits"
  // label - a wait, an ordered wait, and a wait fork. All three reach a body
  // statement through the generic vpiStmt edge; the wait and ordered wait
  // additionally reach a controlling condition through vpiCondition.
  return type == vpiWait || type == vpiOrderedWait || type == vpiWaitFork;
}

VpiHandle VpiWaitConditionExpr(VpiHandle wait) {
  // §37.67: a wait or ordered wait statement reaches its controlling condition
  // through vpiCondition. The diagram routes that edge to either an expression
  // or a sequence instance, so the condition is the first child whose own type
  // is an expression kind or a sequence instance - never the vpiCondition
  // relation tag itself, which is why the generic child walk cannot serve it.
  // Null when none is attached, as for a wait fork, which draws no condition
  // edge.
  if (!wait) return nullptr;
  for (auto* child : wait->children) {
    if (VpiIsExprType(child->type) || child->type == vpiSequenceInst) {
      return child;
    }
  }
  return nullptr;
}

VpiHandle VpiRepeatControlExpr(VpiHandle repeat_control) {
  // §37.69: a repeat control reaches its count expression through the diagram's
  // unlabeled edge to an expr - the vpiExpr relation. The count is the
  // repetition number of an intra-assignment repeat event control ("repeat (n)
  // @(event)"). Its own type is an expression kind (an operation, a constant, a
  // reference,
  // ...) rather than the vpiExpr relation tag, so it is found by scanning for
  // the first expression child; null when none is attached. The repeat
  // control's other unlabeled edge, to the event control, reaches a child whose
  // own type is vpiEventControl and is left to the generic traversal.
  if (!repeat_control) return nullptr;
  for (auto* child : repeat_control->children) {
    if (VpiIsExprType(child->type)) return child;
  }
  return nullptr;
}

bool VpiIsDisableTargetType(int type) {
  // §37.77: the named scopes the disable diagram lists at the far end of the
  // disable's vpiExpr edge - a task, a function, a named begin block, or a
  // named fork block. A disable statement names exactly one of these to
  // terminate.
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
  // §37.77: a disable statement reaches the named scope it disables through
  // vpiExpr. Unlike most vpiExpr targets the scope is not an expression: its
  // own type is a task, function, named begin, or named fork kind rather than
  // the vpiExpr relation tag, so the generic child walk cannot find it. It is
  // located as the disable's first disable-target child; null when none is
  // attached. The companion disable fork form carries no named operand and so
  // is handled by the caller scoping this relation to the plain disable
  // statement.
  if (!disable) return nullptr;
  for (auto* child : disable->children) {
    if (VpiIsDisableTargetType(child->type)) return child;
  }
  return nullptr;
}

bool VpiIsIfOrIfElseType(int type) {
  // §37.71: the two conditional statements the if/if-else diagram groups - a
  // plain if statement and an if-else statement. Both reach a controlling
  // condition expression (vpiCondition) and a then-branch body (the generic
  // vpiStmt edge); the if-else additionally draws an else-branch body
  // (vpiElseStmt).
  return type == vpiIf || type == vpiIfElse;
}

VpiHandle VpiIfConditionExpr(VpiHandle if_stmt) {
  // §37.71: an if or if-else statement reaches its controlling condition
  // through vpiCondition. The condition's own type is an expression kind (an
  // operation, a reference, a constant, ...) rather than the vpiCondition
  // relation tag, so it is found by scanning for the first expression child.
  // The branch bodies are statement children and are skipped by this scan. Null
  // when none is attached.
  if (!if_stmt) return nullptr;
  for (auto* child : if_stmt->children) {
    if (VpiIsExprType(child->type)) return child;
  }
  return nullptr;
}

VpiHandle VpiIfElseStmt(VpiHandle if_stmt) {
  // §37.71: an if-else statement reaches its else-branch body through
  // vpiElseStmt. The then-branch and the else-branch are both body statements
  // (modeled, like every other statement body in this data model, as a vpiStmt
  // child); the generic traversal serves the then-branch as the first such
  // child, so the else-branch is the second one. Its own type is a statement
  // kind rather than the vpiElseStmt relation tag, so the generic walk cannot
  // find it. Null when there is no second body statement (no else branch).
  if (!if_stmt) return nullptr;
  bool seen_then = false;
  for (auto* child : if_stmt->children) {
    if (child->type == vpiStmt) {
      if (seen_then) return child;
      seen_then = true;
    }
  }
  return nullptr;
}

VpiHandle VpiForConditionExpr(VpiHandle for_stmt) {
  // §37.74: a for statement reaches its controlling condition through
  // vpiCondition. As with the other looping and conditional statements, the
  // condition's own type is an expression kind (an operation, a reference, a
  // constant, ...) rather than the vpiCondition relation tag, so it is found by
  // scanning for the first expression child. The for statement's other children
  // - its initialization statements (vpiForInitStmt), increment statements
  // (vpiForIncStmt), and body (vpiStmt) - are statement-edge children that this
  // scan skips. Null when no condition is attached.
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

VpiHandle VpiReturnConditionExpr(VpiHandle return_stmt) {
  // §37.78: a return statement reaches the value it returns through the single
  // edge the diagram draws, labeled vpiCondition. As with the looping and
  // conditional statements (§37.66/§37.71/§37.74/§37.75), that value's own type
  // is an expression kind (an operation, a reference, a constant, ...) rather
  // than the vpiCondition relation tag, so it is found by scanning for the
  // first expression child. A return from a void function or a task carries no
  // value and so has no expression child; the scan then finds nothing and
  // returns null.
  if (!return_stmt) return nullptr;
  for (auto* child : return_stmt->children) {
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
  // first statement child is returned, or null when none is attached.
  if (!delay_control) return nullptr;
  if (delay_control->parent && delay_control->parent->type == vpiAssignment) {
    return nullptr;
  }
  for (auto* child : delay_control->children) {
    if (child->type == vpiStmt) return child;
  }
  return nullptr;
}

// ===========================================================================
// §37.12 Scope.
// ===========================================================================

bool VpiIsBlockItemDeclType(int type) {
  // §37.12 detail 1: a block item declaration is a variable declaration or a
  // type declaration. The variable kinds are the concrete var objects (§37.17);
  // a type declaration is a typedef. A localparam declared in a block is a
  // parameter, which the diagram draws among a scope's members, so it counts as
  // a block item declaration too.
  switch (type) {
    case vpiLogicVar:  // == vpiReg
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
    case vpiArrayVar:  // == vpiRegArray
    case vpiTypedef:
    case vpiParameter:
      return true;
    default:
      return false;
  }
}

bool VpiBlockScopeIsScope(VpiHandle block) {
  // §37.12 detail 1: a named begin or named fork is always a scope. An unnamed
  // begin or unnamed fork is a scope only if it directly contains a block item
  // declaration - a directly-nested declaration, not one buried in a deeper
  // named block. §37.12 detail 2: a for statement is a scope exactly when it
  // declares its loop control variables local to the loop (vpiLocalVarDecls).
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
  // §37.12 details 2 and 3: a loop control variable is a variable - the var
  // kinds a for or foreach statement declares as its index. A type declaration
  // or a parameter, though both block item declarations, is not a loop
  // variable.
  return VpiIsBlockItemDeclType(type) && type != vpiTypedef &&
         type != vpiParameter;
}

// §37.12 detail 7: an array of virtual interfaces is an array variable whose
// elements are virtual interface vars (§37.29). Used to expand the array under
// a scope's vpiVirtualInterfaceVar iteration and to report it as the single
// array var under the scope's vpiVariables iteration.
bool VpiIsVirtualInterfaceArray(VpiHandle obj) {
  if (!obj || !VpiIsArrayVarType(obj->type)) return false;
  for (auto* elem : obj->children) {
    if (elem->type == vpiVirtualInterfaceVar) return true;
  }
  return false;
}

bool VpiIsJoinType(int join_type) {
  // §37.12 detail 6: vpiJoinType is exactly one of these three constants -
  // vpiJoin for a plain join, vpiJoinNone for join_none, vpiJoinAny for
  // join_any. Nothing else is a join type.
  return join_type == vpiJoin || join_type == vpiJoinNone ||
         join_type == vpiJoinAny;
}

bool VpiIsTaskFuncType(int type) {
  // §37.12: the "task func" node groups tasks and functions; the combined
  // vpiTaskFunc kind also denotes one.
  return type == vpiTask || type == vpiFunction || type == vpiTaskFunc;
}

// §37.12 detail 5: a statement child of a task or function body - the kinds a
// task/func groups as its statements. The atomic statements (§37.60) plus the
// block kinds (a begin/fork, named or not) that group several statements.
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
  // §37.12 detail 5: a task or function can have zero or more statements. With
  // none, vpiStmt is null. With more than one, the statements are grouped under
  // an unnamed begin and that begin is the body; with exactly one, that
  // statement is the body. In every nonzero case the body is the task/func's
  // single statement child, so return the first statement child, or null when
  // the body holds no statement.
  if (!task_func) return nullptr;
  for (auto* child : task_func->children) {
    if (VpiIsScopeBodyStmtType(child->type)) return child;
  }
  return nullptr;
}

std::vector<VpiHandle> VpiMultiConcatOperands(
    VpiHandle multiplier, const std::vector<VpiHandle>& concat_exprs) {
  // §37.59 detail 1: the multiplier first, then the concatenation's expressions
  // in order.
  std::vector<VpiHandle> operands;
  operands.reserve(concat_exprs.size() + 1);
  operands.push_back(multiplier);
  operands.insert(operands.end(), concat_exprs.begin(), concat_exprs.end());
  return operands;
}

std::vector<VpiHandle> VpiMultiAssignmentPatternOperands(
    VpiHandle multiplier, const std::vector<VpiHandle>& pattern_exprs) {
  // §37.59 detail 7: the multiplier first, then the assignment pattern's
  // expressions in order - the same shape as a multiconcat (detail 1) but over
  // a distinct operator.
  std::vector<VpiHandle> operands;
  operands.reserve(pattern_exprs.size() + 1);
  operands.push_back(multiplier);
  operands.insert(operands.end(), pattern_exprs.begin(), pattern_exprs.end());
  return operands;
}

std::vector<VpiHandle> VpiCastOpOperands(VpiHandle cast_expr) {
  // §37.59 detail 3: a cast is a unary operation; its only operand is the
  // expression being cast (the target type is the typespec, not an operand).
  return {cast_expr};
}

std::vector<VpiHandle> VpiAssignmentPatternPositionalOperands(
    int slots, const std::vector<VpiAssignmentPatternEntry>& positioned,
    VpiHandle default_value) {
  // §37.59 detail 6: seed every position with the default value, then place
  // each explicitly positioned entry. Iterating the result reproduces the
  // pattern in positional notation; nested patterns stay whole because each
  // value is an opaque handle.
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
  // §37.59 detail 5: guaranteed for a simple expression and a cast operation;
  // guaranteed for an assignment-pattern operation only when its braces are
  // prefixed by a data type name. Any other expression is implementation
  // dependent, so the guarantee does not hold.
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
  // §37.59 detail 9: all three conditions must hold; otherwise FALSE.
  return query.parent_constant_select && query.parent_array_has_static_bounds &&
         query.all_range_exprs_constant;
}

std::string VpiPartSelectParentExpr(std::string_view select_expr) {
  // §37.59 detail 10: remove the trailing bracketed selection. After trimming
  // trailing white space, if the expression ends with ']' the matching '[' is
  // located (honoring nested brackets) and everything from it onward is
  // dropped, yielding the parent expression of Table 37-1.
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
  // §37.59 detail 2: exactly one space between adjacent operands and operators.
  // Empty pieces are skipped so the single-space rule never produces a double
  // space or a leading/trailing space.
  std::string out;
  for (const auto& piece : pieces) {
    if (piece.empty()) continue;
    if (!out.empty()) out.push_back(' ');
    out += piece;
  }
  return out;
}

std::string VpiDecompileParenthesize(std::string_view inner) {
  // §37.59 detail 2: parentheses add no white space - none inside and none
  // around them.
  std::string out = "(";
  out += inner;
  out.push_back(')');
  return out;
}

// ===========================================================================
// §37.42 Task and function call.
// ===========================================================================

bool VpiIsTfCallType(int type) {
  // §37.42: the concrete call kinds the "tf call" class groups.
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

bool VpiIsMethodCallType(int type) {
  // §37.42: the method-call kinds (method func call and method task call).
  return type == vpiMethodFuncCall || type == vpiMethodTaskCall;
}

bool VpiIsTfCallArgumentType(int type) {
  // §37.42: the vpiArgument relation of a tf call reaches an expr, an interface
  // expr, a scope, a primitive, a named event, or a named event array. An expr
  // and an interface expr are themselves groupings, so defer to their
  // classifiers; the rest are concrete kinds.
  if (VpiIsExprType(type) || VpiIsInterfaceExprType(type)) return true;
  switch (type) {
    case vpiScope:
    case vpiNamedEvent:
    case vpiNamedEventArray:
      return true;
    default:
      return VpiObjectIsPrimitive(type);
  }
}

void VpiMakeEmptyArgument(VpiHandle arg) {
  // §37.42 detail 8: an omitted argument is represented as an expression of
  // type vpiOperation whose operator is the null operation.
  if (!arg) return;
  arg->type = vpiOperation;
  arg->op_type = vpiNullOp;
}

void VpiMakeNullArgument(VpiHandle arg) {
  // §37.42 detail 8: an argument that is the special value null is represented
  // as a constant expression whose constant type is the null constant.
  if (!arg) return;
  arg->type = vpiConstant;
  arg->const_type = vpiNullConst;
}

// ===========================================================================
// §37.43 Frames (shared with §37.44's frame--thread edge and vpiActive).
// ===========================================================================

bool VpiIsFrameOriginType(int type) {
  // §37.43 detail 6: the vpiOrigin of a frame is the elaboration-hierarchy
  // point it was activated from. The diagram draws that as a scope, a task or
  // function call (including the system and method forms), or a net or net
  // array - the last covering a frame activated for a nettype's user-defined
  // resolution function.
  switch (type) {
    case vpiScope:
    case vpiTaskCall:
    case vpiFuncCall:
    case vpiSysTaskCall:
    case vpiSysFuncCall:
    case vpiMethodTaskCall:
    case vpiMethodFuncCall:
    case vpiNet:
    case vpiNetArray:
      return true;
    default:
      return false;
  }
}

VpiHandle VpiFrameParent(VpiHandle frame) {
  // §37.43 detail 5: vpiParent reaches the frame from which this child frame
  // was activated, through the parent link when that parent is itself a frame.
  // A root frame (no parent) and a null handle report none. This mirrors
  // §37.44's VpiThreadParent, the same parent-chain relation one level up.
  if (!frame || !frame->parent) return nullptr;
  return frame->parent->type == vpiFrame ? frame->parent : nullptr;
}

VpiHandle VpiFrameOrigin(VpiHandle frame) {
  // §37.43 detail 6: the elaboration-hierarchy point a frame was activated
  // from, modeled as its first origin-kind child.
  if (!frame) return nullptr;
  for (auto* child : frame->children) {
    if (VpiIsFrameOriginType(child->type)) return child;
  }
  return nullptr;
}

VpiHandle VpiFrameStmt(VpiHandle frame) {
  // §37.43 details 4 and 5: the frame-to-stmt transition. For the active frame
  // this is the currently active statement within it; for a parent frame it is
  // the atomic statement or scope whose execution activated the child frame.
  // Either way it is modeled as the frame's first statement child.
  if (!frame) return nullptr;
  for (auto* child : frame->children) {
    if (child->type == vpiStmt) return child;
  }
  return nullptr;
}

VpiHandle VpiFrameThread(VpiHandle frame) {
  // §37.43 (frame--thread edge): the thread a frame belongs to, the reverse of
  // §37.44's VpiThreadFrame. Modeled as the frame's first thread child.
  if (!frame) return nullptr;
  for (auto* child : frame->children) {
    if (child->type == vpiThread) return child;
  }
  return nullptr;
}

std::vector<VpiHandle> VpiFrameAutomatics(VpiHandle frame) {
  // §37.43 detail 1: the vpiAutomatics relation yields a frame's locally
  // declared automatic objects - its variables, named events, and named event
  // arrays - in order. A null handle yields none.
  std::vector<VpiHandle> automatics;
  if (!frame) return automatics;
  for (auto* child : frame->children) {
    // The diagram draws the variables node as the variables class, so accept
    // the class node itself as well as the concrete logic/array variable kinds
    // (§37.17), alongside named events and named event arrays.
    if (child->type == vpiVariables || VpiIsLogicVarType(child->type) ||
        VpiIsArrayVarType(child->type) || child->type == vpiNamedEvent ||
        child->type == vpiNamedEventArray) {
      automatics.push_back(child);
    }
  }
  return automatics;
}

// ===========================================================================
// §37.44 Threads.
// ===========================================================================

VpiHandle VpiThreadParent(VpiHandle thread) {
  // §37.44 (vpiParent -> thread): a thread reaches the thread that spawned it
  // through its parent link, provided that parent is itself a thread. A root
  // thread (no parent) and a null handle report none.
  if (!thread || !thread->parent) return nullptr;
  return thread->parent->type == vpiThread ? thread->parent : nullptr;
}

VpiHandle VpiThreadOrigin(VpiHandle thread) {
  // §37.44 (vpiOrigin -> stmt): the originating statement of a thread, modeled
  // as its first statement child. Null when the handle is null or no origin
  // statement is attached.
  if (!thread) return nullptr;
  for (auto* child : thread->children) {
    if (child->type == vpiStmt) return child;
  }
  return nullptr;
}

VpiHandle VpiThreadFrame(VpiHandle thread) {
  // §37.44 (frame -- thread / detail 1): the frame currently active in the
  // thread, modeled as its first frame child. As tasks and functions are
  // entered new frames are activated, but at most one is active at a time, so a
  // single frame is reported. Null for a null handle or a thread with no frame.
  if (!thread) return nullptr;
  for (auto* child : thread->children) {
    if (child->type == vpiFrame) return child;
  }
  return nullptr;
}

std::vector<VpiHandle> VpiThreadThreads(VpiHandle thread) {
  // §37.44 (thread one-to-many thread): the child threads this thread spawned,
  // as the thread iteration yields them - its thread children, in order.
  std::vector<VpiHandle> threads;
  if (!thread) return threads;
  for (auto* child : thread->children) {
    if (child->type == vpiThread) threads.push_back(child);
  }
  return threads;
}

// ===========================================================================
// §37.22 Object range (shared with §37.17's range relations).
// ===========================================================================

}  // namespace delta
