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
#include "simulator/vpi.h"
// §37.10 detail 3: the package/interface/program instance kinds are defined in
// the SystemVerilog VPI header alongside the §37.10 vpiInstance relation.
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"

namespace delta {

bool VpiIsAssertionType(int type) {
  // §37.49: the kinds the assertion class groups - the concurrent
  // assert/assume/ cover/restrict directives, the three immediate-assertion
  // kinds, and sequence and property instances. Every other object kind is not
  // an assertion.
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
  // §37.34 detail 5: the constraint-item grouping spans the constraint
  // orderings (the solve-before/solve-after relations) and the constraint
  // expressions that make up a constraint. Any other object kind is not a
  // constraint item.
  switch (type) {
    case vpiConstraintOrdering:
    case vpiConstraintExpr:
      return true;
    default:
      return false;
  }
}

bool VpiIsConstraintExprContainerType(int type) {
  // §37.38 detail 3: the constraint-expression kinds that hold a body of
  // further constraint expressions reachable through the vpiConstraintExpr
  // iteration - an implication, a constraint if, a constraint if-else, or a
  // foreach constraint. Any other constraint expression (a distribution, a soft
  // disable, a bare expression) holds no such body.
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

bool VpiIsClassMethodType(int type) {
  // §37.31 detail 1: the vpiMethods relation of a class defn reaches the
  // class's methods, which the diagram draws as the "task func" node - a task
  // or a function declared as a class item. No other object kind is a method.
  switch (type) {
    case vpiFunction:
    case vpiTask:
      return true;
    default:
      return false;
  }
}

bool VpiIsClassMemberValueType(int type) {
  // §37.31 detail 2: the value-access restriction applies to the variable and
  // event handles a class defn hands back - the variables node and the concrete
  // variable kinds (§37.17), a class variable, and the named event / named
  // event array. Anything else reached from a class defn is not value-bearing
  // in this sense. This mirrors the variable/event grouping used for frame
  // automatics (§37.43).
  return type == vpiVariables || VpiIsLogicVarType(type) ||
         VpiIsArrayVarType(type) || type == vpiClassVar ||
         type == vpiNamedEvent || type == vpiNamedEventArray;
}

VpiHandle VpiAssertionClockingBlock(VpiHandle assertion) {
  // §37.49: a concurrent assertion traverses to its governing clocking block
  // through the untagged vpiClockingBlock relation. The association is modeled
  // as a clocking-block child; report the first one, or null when none is
  // present.
  if (!assertion) return nullptr;
  for (auto* child : assertion->children) {
    if (child->type == vpiClockingBlock) return child;
  }
  return nullptr;
}

bool VpiIsConcurrentAssertionType(int type) {
  // §37.50: the concurrent-assertion class is realized by exactly the four
  // directive kinds the diagram draws in its dashed box. Everything else - the
  // immediate kinds and sequence/property instances (§37.49) included - is not
  // a concurrent assertion.
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
  // §37.50: vpiProperty reaches either a property instance or a property
  // specification; no other kind is a concurrent assertion's property.
  return type == vpiPropertyInst || type == vpiPropertySpec;
}

VpiHandle VpiConcurrentAssertionProperty(VpiHandle assertion) {
  // §37.50: traverse to the assertion's property (instance or specification),
  // modeled as the first such child. Null when none is attached.
  if (!assertion) return nullptr;
  for (auto* child : assertion->children) {
    if (VpiIsConcurrentAssertionPropertyType(child->type)) return child;
  }
  return nullptr;
}

VpiHandle VpiConcurrentAssertionClockingEvent(VpiHandle assertion) {
  // §37.50 (detail 1): the clocking event is the actual event the assertion is
  // evaluated on regardless of whether it was explicit or inferred, so the same
  // event-control child is reported in both cases. Null when none is attached.
  if (!assertion) return nullptr;
  for (auto* child : assertion->children) {
    if (child->type == vpiEventControl) return child;
  }
  return nullptr;
}

bool VpiConcurrentAssertionHasPassStmt(int type) {
  // §37.50 (-> stmt / detail 2): assert, assume and cover carry a pass action
  // statement; a restrict has none.
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
  // §37.50 (vpiElseStmt / detail 2): only assert and assume carry an else
  // (fail) action statement. A cover has no else statement and a restrict has
  // no fail statement.
  return type == vpiAssert || type == vpiAssume;
}

VpiHandle VpiConcurrentAssertionStmt(VpiHandle assertion) {
  // §37.50: the pass action statement, modeled as the assertion's first
  // statement child reached through vpiStmt. Null when none is attached.
  if (!assertion) return nullptr;
  for (auto* child : assertion->children) {
    if (child->type == vpiStmt) return child;
  }
  return nullptr;
}

VpiHandle VpiConcurrentAssertionElseStmt(VpiHandle assertion) {
  // §37.50: the else (fail) action statement, modeled as the assertion's first
  // else-statement child reached through vpiElseStmt. Null when none is
  // attached.
  if (!assertion) return nullptr;
  for (auto* child : assertion->children) {
    if (child->type == vpiElseStmt) return child;
  }
  return nullptr;
}

bool VpiConcurrentAssertionIsSimulated(int type) {
  // §37.50 (detail 2): a restrict is not simulated and hence generates no
  // run-time information; every other concurrent assertion kind is simulated.
  return VpiIsConcurrentAssertionType(type) && type != vpiRestrict;
}

bool VpiIsImmediateAssertionType(int type) {
  // §37.55: the three immediate-assertion kinds the diagram draws - immediate
  // assert, immediate assume, and immediate cover. No other object kind is an
  // immediate assertion.
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
  // §37.55 (vpiElseStmt): the diagram routes a vpiElseStmt edge from the
  // immediate assert and immediate assume boxes but not from immediate cover,
  // so only an assert or an assume carries an else (fail) action statement.
  return type == vpiImmediateAssert || type == vpiImmediateAssume;
}

VpiHandle VpiImmediateAssertionExpr(VpiHandle assertion) {
  // §37.55: the asserted expression, reached through vpiExpr and modeled as the
  // assertion's first expression child. Null when none is attached.
  if (!assertion) return nullptr;
  for (auto* child : assertion->children) {
    if (VpiIsExprType(child->type)) return child;
  }
  return nullptr;
}

VpiHandle VpiImmediateAssertionStmt(VpiHandle assertion) {
  // §37.55: the pass action statement, modeled as the assertion's first
  // statement child reached through vpiStmt. Null when none is attached.
  if (!assertion) return nullptr;
  for (auto* child : assertion->children) {
    if (child->type == vpiStmt) return child;
  }
  return nullptr;
}

VpiHandle VpiImmediateAssertionElseStmt(VpiHandle assertion) {
  // §37.55: the else (fail) action statement, modeled as the assertion's first
  // else-statement child reached through vpiElseStmt. Null when none is
  // attached (always the case for an immediate cover).
  if (!assertion) return nullptr;
  for (auto* child : assertion->children) {
    if (child->type == vpiElseStmt) return child;
  }
  return nullptr;
}

bool VpiIsSequenceExprType(int type) {
  // §37.54 (D1): the kinds the sequence-expr class groups - an operation, a
  // sequence instance, a distribution, and a bare boolean expression. The bare
  // expression is abstract in the diagram; its concrete forms used directly as
  // a sequence are a constant and a reference. Every other kind is not a
  // member.
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
  // §37.54 detail 2: exactly these eleven operators may appear as the vpiOpType
  // of a sequence expression's operation.
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

// §37.54 detail 3: a range/bound's upper handle is reported only when it
// differs from the lower one. Passing the same handle (or null) for the upper
// bound models a range whose bounds coincide, so the upper bound is dropped.
static bool VpiRangeUpperDiffers(VpiHandle lower, VpiHandle upper) {
  return upper != nullptr && upper != lower;
}

std::vector<VpiHandle> VpiUnaryCycleDelayOperands(VpiHandle sequence,
                                                  VpiHandle left_range,
                                                  VpiHandle right_range) {
  // §37.54 detail 3a: sequence, left range, then right range (the latter only
  // when it differs from the left range).
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
  // §37.54 detail 3b: left-hand side sequence, right-hand side sequence, left
  // range, then right range (only when it differs from the left range).
  std::vector<VpiHandle> operands = {lhs_sequence, rhs_sequence, left_range};
  if (VpiRangeUpperDiffers(left_range, right_range)) {
    operands.push_back(right_range);
  }
  return operands;
}

std::vector<VpiHandle> VpiRepeatOperands(VpiHandle sequence,
                                         VpiHandle left_bound,
                                         VpiHandle right_bound) {
  // §37.54 detail 3c: the repeated sequence, the left repeat bound, then the
  // right repeat bound (only when it differs from the left bound). The same
  // ordering serves every repeat operator.
  std::vector<VpiHandle> operands = {sequence, left_bound};
  if (VpiRangeUpperDiffers(left_bound, right_bound)) {
    operands.push_back(right_bound);
  }
  return operands;
}

std::vector<VpiHandle> VpiSequenceInstArguments(
    const std::vector<VpiSequenceFormal>& formals,
    const std::vector<VpiHandle>& provided) {
  // §37.54 detail 1: walk the formals in declaration order; use the supplied
  // actual when the instantiation gives one, otherwise fall back to the
  // formal's default value. The result lines up one-to-one with the formals.
  std::vector<VpiHandle> arguments;
  arguments.reserve(formals.size());
  for (size_t i = 0; i < formals.size(); ++i) {
    VpiHandle actual = i < provided.size() ? provided[i] : nullptr;
    arguments.push_back(actual != nullptr ? actual : formals[i].default_value);
  }
  return arguments;
}

bool VpiIsSequenceArgumentType(int type) {
  // §37.54 (D5): a sequence-instance argument is a named event or a sequence
  // expression (the sequence-expr class grouped by VpiIsSequenceExprType).
  return type == vpiNamedEvent || VpiIsSequenceExprType(type);
}

VpiHandle VpiSequenceInstDecl(VpiHandle sequence_inst) {
  // §37.54 (D4): a sequence instance resolves to the sequence declaration it
  // instantiates, modeled as a vpiSequenceDecl child. Report the first one, or
  // null when the handle is null or no declaration is attached.
  if (!sequence_inst) return nullptr;
  for (auto* child : sequence_inst->children) {
    if (child->type == vpiSequenceDecl) return child;
  }
  return nullptr;
}

bool VpiIsMatchItemType(int type) {
  // §37.54 (D6): a sequence match item is an assignment or a task/function
  // call.
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
  // §37.54 (D6): the vpiMatchItem iteration over a bare expression yields its
  // assignment/tf-call children, in order, dropping anything else.
  std::vector<VpiHandle> items;
  if (!expr) return items;
  for (auto* child : expr->children) {
    if (VpiIsMatchItemType(child->type)) items.push_back(child);
  }
  return items;
}

bool VpiIsPropertyExprType(int type) {
  // §37.52: the kinds the property-expr class groups - a (property) operation,
  // a multiclock sequence expression, a property instance, a clocked property,
  // and a case property. The property-expr class selector itself is not a
  // member, and sequence-expr kinds are classified by the sequence-expr class,
  // not here.
  switch (type) {
    case vpiOperation:
    case vpiMulticlockSequenceExpr:
    case vpiPropertyInst:
    case vpiClockedProperty:
    case vpiCaseProperty:
      return true;
    default:
      return false;
  }
}

bool VpiIsPropertyExprOpType(int op) {
  // §37.52 detail 2: exactly these twenty operators may appear as the vpiOpType
  // of a property expression's operation.
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
  // §37.52 detail 2 (vpiNexttimeOp): the property, then the constant. The
  // constant is given only when it differs from 1, so a nexttime whose constant
  // is 1 (or absent) reports just the property.
  std::vector<VpiHandle> operands = {property};
  if (constant != nullptr && constant_differs_from_one) {
    operands.push_back(constant);
  }
  return operands;
}

std::vector<VpiHandle> VpiAlwaysEventuallyOperands(VpiHandle property,
                                                   VpiHandle left_range,
                                                   VpiHandle right_range) {
  // §37.52 detail 2 (vpiAlwaysOp/vpiEventuallyOp): the property, then the left
  // and right range bounds. A bound that is absent (null) is omitted, so an
  // unranged operator yields just the property.
  std::vector<VpiHandle> operands = {property};
  if (left_range != nullptr) operands.push_back(left_range);
  if (right_range != nullptr) operands.push_back(right_range);
  return operands;
}

bool VpiIsOpStrongValidOp(int op) {
  // §37.52 detail 3: vpiOpStrong is valid only for these property operators. It
  // is additionally valid for a sequence expression, whose strength the
  // sequence-expr class governs rather than this property-operator set.
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

bool VpiIsPropertyVariableValueAccessible() {
  // §37.52 detail 1: property variables are declarations whose value cannot be
  // accessed through VPI.
  return false;
}

std::vector<VpiHandle> VpiCaseItemConditions(VpiHandle case_item) {
  // §37.52 detail 4: a case property item groups every case condition that
  // branches to the same property statement. Its condition members are the
  // children other than the property-expr branch (the diagram's case property
  // item -> property expr edge). The default case item carries no condition
  // expression (detail 5), so it groups none.
  std::vector<VpiHandle> conditions;
  if (!case_item) return conditions;
  for (auto* child : case_item->children) {
    if (!VpiIsPropertyExprType(child->type)) conditions.push_back(child);
  }
  return conditions;
}

bool VpiIsDisableConditionType(int type) {
  // §37.52: a property specification's disable condition reaches a bare
  // expression or a distribution. A property instance's disable condition (see
  // §37.51) reaches only an expression, a subset of these kinds.
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
  // §37.52: the clocking event a property spec or clocked property traverses
  // to, modeled as the object's event-control child. Report the first one, or
  // null when the handle is null or no clocking event is attached.
  if (!obj) return nullptr;
  for (auto* child : obj->children) {
    if (child->type == vpiEventControl) return child;
  }
  return nullptr;
}

VpiHandle VpiPropertyExprChild(VpiHandle obj) {
  // §37.52: the property expression reached through a "-> property expr" edge -
  // the object's first property-expr-kind child. Null when none is present.
  if (!obj) return nullptr;
  for (auto* child : obj->children) {
    if (VpiIsPropertyExprType(child->type)) return child;
  }
  return nullptr;
}

std::vector<VpiHandle> VpiPropFormals(VpiHandle property_decl) {
  // §37.51 detail 1: the vpiPropFormalDecl iteration yields the property
  // declaration's formals - its vpiPropFormalDecl children - in declaration
  // order. A null handle yields none.
  std::vector<VpiHandle> formals;
  if (!property_decl) return formals;
  for (auto* child : property_decl->children) {
    if (child->type == vpiPropFormalDecl) formals.push_back(child);
  }
  return formals;
}

int VpiPropFormalDirection(bool is_local_variable_argument) {
  // §37.51 detail 5: a local variable argument is an input; every other formal
  // has no direction.
  return is_local_variable_argument ? vpiInput : vpiNoDirection;
}

VpiHandle VpiPropFormalTypespec(VpiHandle formal) {
  // §37.51 detail 3: a typed formal carries a typespec child; an untyped formal
  // has none, so the relation reports null.
  if (!formal) return nullptr;
  for (auto* child : formal->children) {
    if (child->type == vpiTypespec) return child;
  }
  return nullptr;
}

VpiHandle VpiPropFormalInitExpr(VpiHandle formal) {
  // §37.51 detail 4: a formal's initialization expression is reached through
  // vpiExpr; the diagram draws its target as a named event or a property
  // expression. Report the first such child, or null when the formal has none.
  if (!formal) return nullptr;
  for (auto* child : formal->children) {
    if (child->type == vpiNamedEvent || VpiIsPropertyExprType(child->type)) {
      return child;
    }
  }
  return nullptr;
}

std::vector<VpiHandle> VpiPropertyInstArguments(
    const std::vector<VpiPropertyFormal>& formals,
    const std::vector<VpiHandle>& provided) {
  // §37.51 detail 2: walk the formals in declaration order; use the supplied
  // actual when the instantiation gives one, otherwise fall back to the
  // formal's default value. The result lines up one-to-one with the formals, so
  // each argument corresponds to its respective formal.
  std::vector<VpiHandle> arguments;
  arguments.reserve(formals.size());
  for (size_t i = 0; i < formals.size(); ++i) {
    VpiHandle actual = i < provided.size() ? provided[i] : nullptr;
    arguments.push_back(actual != nullptr ? actual : formals[i].default_value);
  }
  return arguments;
}

bool VpiIsPropertyArgumentType(int type) {
  // §37.51: a property-instance argument is a named event or a property
  // expression (the property-expr class grouped by VpiIsPropertyExprType).
  return type == vpiNamedEvent || VpiIsPropertyExprType(type);
}

VpiHandle VpiPropertyInstDecl(VpiHandle property_inst) {
  // §37.51: a property instance resolves to the property declaration it
  // instantiates, modeled as a vpiPropertyDecl child. Report the first one, or
  // null when the handle is null or no declaration is attached.
  if (!property_inst) return nullptr;
  for (auto* child : property_inst->children) {
    if (child->type == vpiPropertyDecl) return child;
  }
  return nullptr;
}

std::vector<VpiHandle> VpiMulticlockSequenceClockedSeqs(
    VpiHandle multiclock_seq) {
  // §37.56: the multiclock sequence expr -> clocked seq edge is a one-to-many
  // (double arrow) tagless relation, i.e. the vpiClockedSeq iteration. Return
  // the multiclock sequence expression's clocked-seq children in order,
  // dropping anything else. A null handle yields none.
  std::vector<VpiHandle> clocked_seqs;
  if (!multiclock_seq) return clocked_seqs;
  for (auto* child : multiclock_seq->children) {
    if (child->type == vpiClockedSeq) clocked_seqs.push_back(child);
  }
  return clocked_seqs;
}

VpiHandle VpiClockedSeqSequenceExpr(VpiHandle clocked_seq) {
  // §37.56: the clocked seq -> sequence expr edge is a one-to-one (single
  // arrow) tagless relation, vpi_handle(vpiSequenceExpr, ...). Report the
  // clocked seq's first sequence-expr-kind child (the sequence-expr class of
  // §37.54), or null when the handle is null or no sequence expression is
  // attached.
  if (!clocked_seq) return nullptr;
  for (auto* child : clocked_seq->children) {
    if (VpiIsSequenceExprType(child->type)) return child;
  }
  return nullptr;
}

std::vector<VpiHandle> VpiSeqFormals(VpiHandle sequence_decl) {
  // §37.53 detail 1: the vpiSeqFormalDecl iteration yields the sequence
  // declaration's formals - its vpiSeqFormalDecl children - in declaration
  // order. A null handle yields none.
  std::vector<VpiHandle> formals;
  if (!sequence_decl) return formals;
  for (auto* child : sequence_decl->children) {
    if (child->type == vpiSeqFormalDecl) formals.push_back(child);
  }
  return formals;
}

VpiHandle VpiSeqDeclBodyExpr(VpiHandle sequence_decl) {
  // §37.53: a sequence declaration's body is reached through vpiExpr; the
  // diagram draws its target as a sequence expression (the sequence-expr class)
  // or a multiclock sequence expression. Report the first such child, or null
  // when none is present.
  if (!sequence_decl) return nullptr;
  for (auto* child : sequence_decl->children) {
    if (VpiIsSequenceExprType(child->type) ||
        child->type == vpiMulticlockSequenceExpr) {
      return child;
    }
  }
  return nullptr;
}

int VpiSeqFormalDirection(bool is_local_variable_argument,
                          int local_direction) {
  // §37.53 detail 4: a formal that is not a local variable argument has no
  // direction; a local variable argument reports its declared direction (one of
  // input, output, or inout).
  return is_local_variable_argument ? local_direction : vpiNoDirection;
}

VpiHandle VpiSeqFormalTypespec(VpiHandle formal) {
  // §37.53 detail 2: a typed formal carries a typespec child; an untyped formal
  // has none, so the relation reports null.
  if (!formal) return nullptr;
  for (auto* child : formal->children) {
    if (child->type == vpiTypespec) return child;
  }
  return nullptr;
}

VpiHandle VpiSeqFormalInitExpr(VpiHandle formal) {
  // §37.53 detail 3: a formal's initialization expression is reached through
  // vpiExpr; the diagram draws its target as a named event or a sequence
  // expression. Report the first such child, or null when the formal has none.
  if (!formal) return nullptr;
  for (auto* child : formal->children) {
    if (child->type == vpiNamedEvent || VpiIsSequenceExprType(child->type)) {
      return child;
    }
  }
  return nullptr;
}

// ===========================================================================
// §37.57 Let.
// ===========================================================================

std::vector<VpiHandle> VpiLetExprArguments(
    const std::vector<VpiLetFormal>& formals,
    const std::vector<VpiHandle>& provided) {
  // §37.57 detail 1: the vpiArgument iteration returns a let expression's
  // arguments in the order the let's formals are declared, so each argument
  // corresponds to its formal. Walk the formals in that order, taking the
  // actual the instantiation supplied; when it omits one, fall back to that
  // formal's default value so the result still lines up one-to-one with the
  // formals.
  std::vector<VpiHandle> arguments;
  arguments.reserve(formals.size());
  for (size_t i = 0; i < formals.size(); ++i) {
    VpiHandle actual = i < provided.size() ? provided[i] : nullptr;
    arguments.push_back(actual != nullptr ? actual : formals[i].default_value);
  }
  return arguments;
}

// ===========================================================================
// §37.58 Simple expressions.
// ===========================================================================

bool VpiSimpleExprVectorUseAccessesUse(bool references_vector,
                                       bool references_part_select_of_vector,
                                       bool references_bit_select_of_vector) {
  // §37.58 detail 1: for a vector simple expression, the vpiUse relation
  // reaches every use of the vector itself as well as every use of any of its
  // part-selects or bit-selects. A candidate use therefore counts whenever it
  // references the vector or one of those derived selects.
  return references_vector || references_part_select_of_vector ||
         references_bit_select_of_vector;
}

bool VpiSimpleExprBitSelectUseAccessesUse(
    bool references_this_bit, bool references_parent_vector,
    bool references_part_select_containing_bit) {
  // §37.58 detail 2: for a bit-select, the vpiUse relation reaches every use of
  // that specific bit, every use of the parent vector, and every part-select of
  // the parent that contains the bit. A candidate use counts when it references
  // any of those three.
  return references_this_bit || references_parent_vector ||
         references_part_select_containing_bit;
}

bool VpiSimpleExprBitSelectConstantSelect(bool all_indices_constant,
                                          bool parent_constant_select) {
  // §37.58 detail 3: vpiConstantSelect of a bit-select is TRUE only when every
  // associated index expression is an elaboration-time constant and
  // vpiConstantSelect is itself TRUE for the bit-select's parent; otherwise it
  // is FALSE.
  return all_indices_constant && parent_constant_select;
}

// ===========================================================================
// §37.61 Dynamic prefixing.
// ===========================================================================

bool VpiIsDynamicPrefixSourceType(int type) {
  // §37.61 detail 1: the object kinds whose vpiPrefix relation this subclause
  // serves - a simple expression (its concrete reference and bit-select kinds),
  // a part-select, an indexed part-select, a named event, and a named event
  // array. A tf call is in the diagram too, but a method call's prefix is owned
  // by §37.42, so tf-call kinds are deliberately left out here.
  switch (type) {
    case vpiRefObj:     // the concrete simple expression
    case vpiBitSelect:  // a bit-select is also a simple expression
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
  // §37.61 detail 3: vpiHasActual is TRUE for an object that is all or part of
  // a statically declared object in an elaborated context, or an automatic
  // variable obtained from a frame (§37.43); it is FALSE for an object obtained
  // from a lexical context such as a class defn (§37.31), one referenced
  // relative to its class typespec (§37.32), or an automatic variable obtained
  // from a task or function declaration (§37.41). When the provenance does not
  // pin the answer, it tracks whether the object has a corresponding actual at
  // the current simulation time.
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

// ===========================================================================
// §37.59 Expressions.
// ===========================================================================

}  // namespace delta
