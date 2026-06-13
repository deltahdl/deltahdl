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
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
// §37.10 detail 3: the package/interface/program instance kinds are defined in
// the SystemVerilog VPI header alongside the §37.10 vpiInstance relation.
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"

namespace delta {

VpiContext::~VpiContext() {
  for (auto* obj : all_objects_) {
    delete obj;
  }
}

VpiHandle VpiContext::AllocObject() {
  auto* obj = new VpiObject();
  all_objects_.push_back(obj);
  return obj;
}

// §37.3.7: derive the reported allocation scheme from how the object was
// allocated. Frame/thread allocations are Automatic, dynamic-memory (class)
// allocations are Dynamic, and everything else falls through to the mandated
// Other default.
int VpiAllocSchemeFor(VpiAllocKind kind) {
  switch (kind) {
    case VpiAllocKind::kFrameOrThread:
      return kVpiAutomaticScheme;
    case VpiAllocKind::kDynamic:
      return kVpiDynamicScheme;
    case VpiAllocKind::kOther:
      return kVpiOtherScheme;
  }
  return kVpiOtherScheme;
}

// §37.10 details 1 and 10: keep only the entries that are user-defined and
// explicitly declared in the instance, in their original order. Built-in
// definitions and entries merely made visible (e.g. by import) are dropped.
static std::vector<const VpiTypeDeclEntry*> FilterDeclaredUserEntries(
    const std::vector<VpiTypeDeclEntry>& entries) {
  std::vector<const VpiTypeDeclEntry*> visible;
  for (const auto& entry : entries) {
    if (entry.user_defined && entry.declared_in_instance) {
      visible.push_back(&entry);
    }
  }
  return visible;
}

std::vector<const VpiTypeDeclEntry*> VpiInstanceTypedefs(
    const std::vector<VpiTypeDeclEntry>& entries) {
  return FilterDeclaredUserEntries(entries);
}

std::vector<const VpiTypeDeclEntry*> VpiInstanceNetTypedefs(
    const std::vector<VpiTypeDeclEntry>& entries) {
  return FilterDeclaredUserEntries(entries);
}

bool VpiIsInstanceType(int type) {
  // §37.10 detail 3: an instance is a package, module, interface, or program.
  return type == kVpiModule || type == vpiPackage || type == vpiInterface ||
         type == vpiProgram;
}

VpiHandle VpiInstanceOf(VpiHandle obj) {
  // §37.10 detail 3: walk outward to the first enclosing scope that is itself
  // an instance; that is the immediate instance the object is instantiated in.
  if (!obj) return nullptr;
  for (VpiObject* scope = obj->parent; scope != nullptr;
       scope = scope->parent) {
    if (VpiIsInstanceType(scope->type)) return scope;
  }
  return nullptr;
}

VpiHandle VpiModuleOf(VpiHandle obj) {
  // §37.10 detail 2: report the nearest enclosing module, or null when no
  // module encloses the object.
  if (!obj) return nullptr;
  for (VpiObject* scope = obj->parent; scope != nullptr;
       scope = scope->parent) {
    if (scope->type == kVpiModule) return scope;
  }
  return nullptr;
}

int VpiMemoryIterationItemType() {
  // §37.10 detail 4: the iteration yields array variable objects, never the
  // legacy vpiMemory object kind.
  return vpiRegArray;
}

std::string VpiCompilationUnitFullName(std::string_view object_path) {
  // §37.10 detail 5: such names begin with the "$unit::" scope name.
  return "$unit::" + std::string(object_path);
}

std::string VpiPackageFullName(std::string_view package_name) {
  // §37.10 detail 5: a package's full name is its own name ending in "::".
  return std::string(package_name) + "::";
}

std::string VpiPackageMemberFullName(std::string_view package_name,
                                     std::string_view member_path) {
  // §37.10 detail 5: package name, the "::" separator, then the member path.
  return std::string(package_name) + "::" + std::string(member_path);
}

std::string_view VpiNameSeparator(bool package_or_class_defn_boundary) {
  // §37.10 detail 5: "::" follows a package or class-definition scope; "." is
  // used in every other case.
  return package_or_class_defn_boundary ? "::" : ".";
}

bool VpiHandleByNameAccessible(const VpiObject& obj) {
  // §37.10 detail 6: imported items and compilation-unit objects are not
  // reachable through vpi_handle_by_name().
  return !obj.imported && !obj.in_compilation_unit;
}

int VpiSmallestTimePrecision(const std::vector<int>& precisions) {
  // §37.10 detail 7: the smallest (finest) precision wins; nothing to report
  // when the design has no modules.
  if (precisions.empty()) return 0;
  int smallest = precisions.front();
  for (int precision : precisions) {
    if (precision < smallest) smallest = precision;
  }
  return smallest;
}

bool VpiIsAssertionType(int type) {
  // §37.49: the kinds the assertion class groups - the concurrent assert/assume/
  // cover/restrict directives, the three immediate-assertion kinds, and sequence
  // and property instances. Every other object kind is not an assertion.
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
  // §37.34 detail 5: the constraint-item grouping spans the constraint orderings
  // (the solve-before/solve-after relations) and the constraint expressions that
  // make up a constraint. Any other object kind is not a constraint item.
  switch (type) {
    case vpiConstraintOrdering:
    case vpiConstraintExpr:
      return true;
    default:
      return false;
  }
}

bool VpiIsConstraintExprContainerType(int type) {
  // §37.38 detail 3: the constraint-expression kinds that hold a body of further
  // constraint expressions reachable through the vpiConstraintExpr iteration - an
  // implication, a constraint if, a constraint if-else, or a foreach constraint.
  // Any other constraint expression (a distribution, a soft disable, a bare
  // expression) holds no such body.
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
  // §37.31 detail 1: the vpiMethods relation of a class defn reaches the class's
  // methods, which the diagram draws as the "task func" node - a task or a
  // function declared as a class item. No other object kind is a method.
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
  // variable kinds (§37.17), a class variable, and the named event / named event
  // array. Anything else reached from a class defn is not value-bearing in this
  // sense. This mirrors the variable/event grouping used for frame automatics
  // (§37.43).
  return type == vpiVariables || VpiIsLogicVarType(type) ||
         VpiIsArrayVarType(type) || type == vpiClassVar ||
         type == vpiNamedEvent || type == vpiNamedEventArray;
}

VpiHandle VpiAssertionClockingBlock(VpiHandle assertion) {
  // §37.49: a concurrent assertion traverses to its governing clocking block
  // through the untagged vpiClockingBlock relation. The association is modeled as
  // a clocking-block child; report the first one, or null when none is present.
  if (!assertion) return nullptr;
  for (auto* child : assertion->children) {
    if (child->type == vpiClockingBlock) return child;
  }
  return nullptr;
}

bool VpiIsConcurrentAssertionType(int type) {
  // §37.50: the concurrent-assertion class is realized by exactly the four
  // directive kinds the diagram draws in its dashed box. Everything else - the
  // immediate kinds and sequence/property instances (§37.49) included - is not a
  // concurrent assertion.
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
  // §37.50 (vpiElseStmt / detail 2): only assert and assume carry an else (fail)
  // action statement. A cover has no else statement and a restrict has no fail
  // statement.
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
  // else-statement child reached through vpiElseStmt. Null when none is attached.
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
  // immediate assert and immediate assume boxes but not from immediate cover, so
  // only an assert or an assume carries an else (fail) action statement.
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
  // else-statement child reached through vpiElseStmt. Null when none is attached
  // (always the case for an immediate cover).
  if (!assertion) return nullptr;
  for (auto* child : assertion->children) {
    if (child->type == vpiElseStmt) return child;
  }
  return nullptr;
}

bool VpiIsSequenceExprType(int type) {
  // §37.54 (D1): the kinds the sequence-expr class groups - an operation, a
  // sequence instance, a distribution, and a bare boolean expression. The bare
  // expression is abstract in the diagram; its concrete forms used directly as a
  // sequence are a constant and a reference. Every other kind is not a member.
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

// §37.54 detail 3: a range/bound's upper handle is reported only when it differs
// from the lower one. Passing the same handle (or null) for the upper bound
// models a range whose bounds coincide, so the upper bound is dropped.
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
  // actual when the instantiation gives one, otherwise fall back to the formal's
  // default value. The result lines up one-to-one with the formals.
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
  // §37.54 (D6): a sequence match item is an assignment or a task/function call.
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
  // §37.52: the kinds the property-expr class groups - a (property) operation, a
  // multiclock sequence expression, a property instance, a clocked property, and
  // a case property. The property-expr class selector itself is not a member, and
  // sequence-expr kinds are classified by the sequence-expr class, not here.
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

std::vector<VpiHandle> VpiNexttimeOperands(VpiHandle property, VpiHandle constant,
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
  // §37.52: the clocking event a property spec or clocked property traverses to,
  // modeled as the object's event-control child. Report the first one, or null
  // when the handle is null or no clocking event is attached.
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
  // actual when the instantiation gives one, otherwise fall back to the formal's
  // default value. The result lines up one-to-one with the formals, so each
  // argument corresponds to its respective formal.
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
  // (double arrow) tagless relation, i.e. the vpiClockedSeq iteration. Return the
  // multiclock sequence expression's clocked-seq children in order, dropping
  // anything else. A null handle yields none.
  std::vector<VpiHandle> clocked_seqs;
  if (!multiclock_seq) return clocked_seqs;
  for (auto* child : multiclock_seq->children) {
    if (child->type == vpiClockedSeq) clocked_seqs.push_back(child);
  }
  return clocked_seqs;
}

VpiHandle VpiClockedSeqSequenceExpr(VpiHandle clocked_seq) {
  // §37.56: the clocked seq -> sequence expr edge is a one-to-one (single arrow)
  // tagless relation, vpi_handle(vpiSequenceExpr, ...). Report the clocked seq's
  // first sequence-expr-kind child (the sequence-expr class of §37.54), or null
  // when the handle is null or no sequence expression is attached.
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
  // §37.53: a sequence declaration's body is reached through vpiExpr; the diagram
  // draws its target as a sequence expression (the sequence-expr class) or a
  // multiclock sequence expression. Report the first such child, or null when
  // none is present.
  if (!sequence_decl) return nullptr;
  for (auto* child : sequence_decl->children) {
    if (VpiIsSequenceExprType(child->type) ||
        child->type == vpiMulticlockSequenceExpr) {
      return child;
    }
  }
  return nullptr;
}

int VpiSeqFormalDirection(bool is_local_variable_argument, int local_direction) {
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
  // corresponds to its formal. Walk the formals in that order, taking the actual
  // the instantiation supplied; when it omits one, fall back to that formal's
  // default value so the result still lines up one-to-one with the formals.
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
    case vpiRefObj:            // the concrete simple expression
    case vpiBitSelect:         // a bit-select is also a simple expression
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
  // §37.61 detail 3: vpiHasActual is TRUE for an object that is all or part of a
  // statically declared object in an elaborated context, or an automatic
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
  // §37.60: the members drawn inside the atomic stmt class. The waits, disables,
  // and tf call entries are themselves groupings; their concrete kinds (the wait,
  // the disable, and the task/system-task calls) stand in for them here.
  switch (type) {
    case vpiIf:
    case vpiIfElse:
    case vpiWhile:
    case vpiRepeat:
    case vpiWait:           // the "waits" grouping
    case vpiCase:
    case vpiFor:
    case vpiDelayControl:
    case vpiEventControl:
    case vpiEventStmt:
    case vpiAssignment:
    case vpiAssignStmt:
    case vpiDeassign:
    case vpiDisable:        // the "disables" grouping
    case vpiTaskCall:       // the "tf call" grouping: a task call ...
    case vpiSysTaskCall:    // ... or a system-task call
    case vpiForever:
    case vpiForce:
    case vpiRelease:
    case vpiDoWhile:
    case vpiExpectStmt:
    case vpiForeachStmt:
    case vpiImmediateAssert:
    // vpiReturn shares this constant value with vpiImmediateAssume in this header
    // set, so the return statement is classified through the same case.
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
  // §37.64 detail 1: an assignment operator reports the operator combined with the
  // assignment, per 11.4.1. The plain "=" and "<=" forms are normal assignments and
  // report vpiAssignmentOp, as does any spelling that is not an assignment operator.
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
  // vpiAlwaysLatch name the three specialized always_comb/always_ff/always_latch
  // forms. Nothing else is an always type.
  return always_type == vpiAlways || always_type == vpiAlwaysComb ||
         always_type == vpiAlwaysFF || always_type == vpiAlwaysLatch;
}

VpiHandle VpiEventControlStmt(VpiHandle event_control) {
  // §37.65 detail 1: an event control reaches the statement it guards through
  // vpiStmt. When the event control is associated with an assignment - i.e. it is
  // the event control drawn on an assignment object (§37.64) - that statement is
  // always null, since the assignment itself is the action and there is no
  // separate guarded statement. For any other event control the first statement
  // child is returned, or null when none is attached.
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
  // §37.66: the two looping statements the while/repeat diagram groups together -
  // a while statement and a repeat statement. Both reach a controlling condition
  // expression (vpiCondition) and a body statement (vpiStmt) through the same
  // relations.
  return type == vpiWhile || type == vpiRepeat;
}

VpiHandle VpiLoopConditionExpr(VpiHandle loop) {
  // §37.66: a while or repeat statement reaches its controlling condition through
  // vpiCondition. The condition is an expression child whose own type is an
  // expression kind (an operation, a reference, a constant, ...) rather than the
  // vpiCondition relation tag, so it is found by scanning for the first expression
  // child. Null when none is attached.
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
  // through vpiCondition. The diagram routes that edge to either an expression or
  // a sequence instance, so the condition is the first child whose own type is an
  // expression kind or a sequence instance - never the vpiCondition relation tag
  // itself, which is why the generic child walk cannot serve it. Null when none is
  // attached, as for a wait fork, which draws no condition edge.
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
  // unlabeled edge to an expr - the vpiExpr relation. The count is the repetition
  // number of an intra-assignment repeat event control ("repeat (n) @(event)").
  // Its own type is an expression kind (an operation, a constant, a reference,
  // ...) rather than the vpiExpr relation tag, so it is found by scanning for the
  // first expression child; null when none is attached. The repeat control's
  // other unlabeled edge, to the event control, reaches a child whose own type is
  // vpiEventControl and is left to the generic traversal.
  if (!repeat_control) return nullptr;
  for (auto* child : repeat_control->children) {
    if (VpiIsExprType(child->type)) return child;
  }
  return nullptr;
}

bool VpiIsDisableTargetType(int type) {
  // §37.77: the named scopes the disable diagram lists at the far end of the
  // disable's vpiExpr edge - a task, a function, a named begin block, or a named
  // fork block. A disable statement names exactly one of these to terminate.
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
  // vpiExpr. Unlike most vpiExpr targets the scope is not an expression: its own
  // type is a task, function, named begin, or named fork kind rather than the
  // vpiExpr relation tag, so the generic child walk cannot find it. It is located
  // as the disable's first disable-target child; null when none is attached. The
  // companion disable fork form carries no named operand and so is handled by the
  // caller scoping this relation to the plain disable statement.
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
  // §37.71: an if or if-else statement reaches its controlling condition through
  // vpiCondition. The condition's own type is an expression kind (an operation,
  // a reference, a constant, ...) rather than the vpiCondition relation tag, so
  // it is found by scanning for the first expression child. The branch bodies
  // are statement children and are skipped by this scan. Null when none is
  // attached.
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
  // scanning for the first expression child. The for statement's other children -
  // its initialization statements (vpiForInitStmt), increment statements
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
  // relation tag, so it is found by scanning for the first expression child. The
  // do-while's body, drawn by the diagram's unlabeled edge to a statement, is a
  // statement-edge child that this scan skips. Null when no condition is attached.
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
  // than the vpiCondition relation tag, so it is found by scanning for the first
  // expression child. A return from a void function or a task carries no value
  // and so has no expression child; the scan then finds nothing and returns null.
  if (!return_stmt) return nullptr;
  for (auto* child : return_stmt->children) {
    if (VpiIsExprType(child->type)) return child;
  }
  return nullptr;
}

VpiHandle VpiDelayControlStmt(VpiHandle delay_control) {
  // §37.68 detail 1: a delay control reaches the statement it guards through
  // vpiStmt. When the delay control is associated with an assignment - i.e. it
  // is the delay control drawn on an assignment object (§37.64) - that statement
  // is always null, since the assignment itself is the action and there is no
  // separate guarded statement. For any other delay control the first statement
  // child is returned, or null when none is attached.
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
  // §37.12 details 2 and 3: a loop control variable is a variable - the var kinds
  // a for or foreach statement declares as its index. A type declaration or a
  // parameter, though both block item declarations, is not a loop variable.
  return VpiIsBlockItemDeclType(type) && type != vpiTypedef &&
         type != vpiParameter;
}

// §37.12 detail 7: an array of virtual interfaces is an array variable whose
// elements are virtual interface vars (§37.29). Used to expand the array under
// a scope's vpiVirtualInterfaceVar iteration and to report it as the single
// array var under the scope's vpiVariables iteration.
static bool VpiIsVirtualInterfaceArray(VpiHandle obj) {
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
static bool VpiIsScopeBodyStmtType(int type) {
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
  // expressions in order - the same shape as a multiconcat (detail 1) but over a
  // distinct operator.
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
  // §37.59 detail 6: seed every position with the default value, then place each
  // explicitly positioned entry. Iterating the result reproduces the pattern in
  // positional notation; nested patterns stay whole because each value is an
  // opaque handle.
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
  // located (honoring nested brackets) and everything from it onward is dropped,
  // yielding the parent expression of Table 37-1.
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
  // §37.42 detail 8: an omitted argument is represented as an expression of type
  // vpiOperation whose operator is the null operation.
  if (!arg) return;
  arg->type = vpiOperation;
  arg->op_type = vpiNullOp;
}

void VpiMakeNullArgument(VpiHandle arg) {
  // §37.42 detail 8: an argument that is the special value null is represented as
  // a constant expression whose constant type is the null constant.
  if (!arg) return;
  arg->type = vpiConstant;
  arg->const_type = vpiNullConst;
}

// ===========================================================================
// §37.43 Frames (shared with §37.44's frame--thread edge and vpiActive).
// ===========================================================================

bool VpiIsFrameOriginType(int type) {
  // §37.43 detail 6: the vpiOrigin of a frame is the elaboration-hierarchy point
  // it was activated from. The diagram draws that as a scope, a task or function
  // call (including the system and method forms), or a net or net array - the
  // last covering a frame activated for a nettype's user-defined resolution
  // function.
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
  // §37.43 detail 5: vpiParent reaches the frame from which this child frame was
  // activated, through the parent link when that parent is itself a frame. A
  // root frame (no parent) and a null handle report none. This mirrors §37.44's
  // VpiThreadParent, the same parent-chain relation one level up.
  if (!frame || !frame->parent) return nullptr;
  return frame->parent->type == vpiFrame ? frame->parent : nullptr;
}

VpiHandle VpiFrameOrigin(VpiHandle frame) {
  // §37.43 detail 6: the elaboration-hierarchy point a frame was activated from,
  // modeled as its first origin-kind child.
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
    // The diagram draws the variables node as the variables class, so accept the
    // class node itself as well as the concrete logic/array variable kinds
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

bool VpiDimensionRangeIsEmpty(VpiDimensionKind kind) {
  // §37.22 detail 1: dynamic-array, queue, and associative dimensions have no
  // fixed bounds and are represented by an empty range. Fixed packed and
  // unpacked dimensions are not empty.
  switch (kind) {
    case VpiDimensionKind::kDynamic:
    case VpiDimensionKind::kQueue:
    case VpiDimensionKind::kAssoc:
      return true;
    case VpiDimensionKind::kPacked:
    case VpiDimensionKind::kFixedUnpacked:
      return false;
  }
  return false;
}

int VpiRangeSize(const VpiRangeDesc& range) {
  // §37.22 detail 2: an empty range reports a size of 0.
  return range.empty ? 0 : range.size;
}

VpiHandle VpiRangeLeftRange(const VpiRangeDesc& range) {
  // §37.22 detail 2: an empty range returns NULL for vpiLeftRange.
  return range.empty ? nullptr : range.left_expr;
}

VpiHandle VpiRangeRightRange(const VpiRangeDesc& range) {
  // §37.22 detail 2: an empty range returns NULL for vpiRightRange.
  return range.empty ? nullptr : range.right_expr;
}

// ===========================================================================
// §37.17 Variables.
// ===========================================================================

bool VpiIsLogicVarType(int type) {
  // §37.17 detail 19: a logic var and a reg are the same object kind.
  return type == vpiLogicVar || type == kVpiReg;
}

bool VpiIsArrayVarType(int type) {
  // §37.17 detail 19: an array var and a reg array are the same object kind.
  return type == vpiArrayVar || type == vpiRegArray;
}

bool VpiIsArrayVar(int unpacked_range_count) {
  // §37.17 detail 1: one or more unpacked ranges makes a variable an array var.
  return unpacked_range_count >= 1;
}

bool VpiVariableIsArrayMember(VpiHandle var) {
  // §37.17 detail 2: a variable is an array member when its vpiParent prefix is
  // an array variable.
  return var != nullptr && var->parent != nullptr &&
         VpiIsArrayVarType(var->parent->type);
}

bool VpiVariableIsStructUnionMember(VpiHandle var) {
  // §37.17 detail 17: a variable is a struct/union member when its vpiParent
  // prefix is a struct or union variable.
  if (!var || !var->parent) return false;
  return var->parent->type == vpiStructVar || var->parent->type == vpiUnionVar;
}

bool VpiIsPackedArrayVarElementType(int type) {
  // §37.18 detail 3: a packed array variable's subelements are packed struct
  // var, union var, or enum var objects; for a multidimensioned packed array a
  // subelement is itself another packed array var (the leftmost packed range
  // removed). vpiElement walks exactly these kinds.
  switch (type) {
    case vpiStructVar:
    case vpiUnionVar:
    case vpiEnumVar:
    case vpiPackedArrayVar:
      return true;
    default:
      return false;
  }
}

bool VpiVariableIsPackedArrayMember(VpiHandle var) {
  // §37.18 detail 4: vpiPackedArrayMember is TRUE for a struct var, union var,
  // enum var, or packed array var whose vpiParent prefix is a packed array var.
  // The vpiParent prefix is resolved by §37.17 detail 26; here the property is
  // simply that prefix being a packed array var with the element being one of
  // those four kinds.
  if (!var || !var->parent || var->parent->type != vpiPackedArrayVar) {
    return false;
  }
  return VpiIsPackedArrayVarElementType(var->type);
}

bool VpiVarSelectConstantSelect(const VpiVarSelectConstantSelectQuery& query) {
  // §37.19 detail 1: a var select is a constant select only when all three
  // conditions hold together - every index is an elaboration-time constant, the
  // parent is an unpacked array with static bounds, and the parent is itself a
  // constant select. If any condition fails the property is FALSE.
  return query.all_indices_constant && query.parent_is_unpacked_static_array &&
         query.parent_constant_select;
}

VpiHandle VpiVariableInitExpr(VpiHandle var) {
  // §37.17 detail 8: when a variable has an initialization expression, it is
  // reached through vpiExpr - modeled as the variable's first child. A variable
  // with no initialization expression has none.
  if (!var || var->children.empty()) return nullptr;
  return var->children.front();
}

bool VpiSizeChangeCallbackApplies(int array_type, bool is_string_var) {
  // §37.17 detail 14: cbSizeChange applies only to dynamic arrays, associative
  // arrays, queues, and string variables; not to fixed-size (static) arrays or
  // any other variable.
  if (is_string_var) return true;
  return array_type == vpiDynamicArray || array_type == vpiAssocArray ||
         array_type == vpiQueueArray;
}

std::vector<VpiRangeDesc> VpiArrayVarRanges(
    const std::vector<VpiArrayDimension>& dims) {
  // §37.17 detail 4: one range per dimension, leftmost to rightmost. Each
  // dimension routes through §37.22: a dynamic/queue/associative dimension is an
  // empty range, a fixed dimension keeps its bounds. The implicit range of a
  // packed struct/union element or an enum var's base type is excluded.
  std::vector<VpiRangeDesc> ranges;
  for (const auto& dim : dims) {
    if (dim.implicit_element_range) continue;
    VpiRangeDesc range;
    range.empty = VpiDimensionRangeIsEmpty(dim.kind);
    range.left_expr = dim.left_expr;
    range.right_expr = dim.right_expr;
    range.size = dim.size;
    ranges.push_back(range);
  }
  return ranges;
}

// §37.17 detail 6: build the §37.22 range for a variable's leftmost dimension,
// the one vpiLeftRange/vpiRightRange report. Returns an empty range (so both
// relations yield NULL) when the variable has no members or no dimensions.
static VpiRangeDesc LeftmostVariableRange(
    const std::vector<VpiArrayDimension>& dims, bool has_members) {
  if (!has_members || dims.empty()) {
    VpiRangeDesc empty;
    empty.empty = true;
    return empty;
  }
  const VpiArrayDimension& dim = dims.front();
  VpiRangeDesc range;
  range.empty = VpiDimensionRangeIsEmpty(dim.kind);
  range.left_expr = dim.left_expr;
  range.right_expr = dim.right_expr;
  range.size = dim.size;
  return range;
}

VpiHandle VpiVariableLeftRange(const std::vector<VpiArrayDimension>& dims,
                               bool has_members) {
  // §37.17 detail 6: defer to §37.22's vpiLeftRange, which returns NULL for an
  // empty leftmost range.
  return VpiRangeLeftRange(LeftmostVariableRange(dims, has_members));
}

VpiHandle VpiVariableRightRange(const std::vector<VpiArrayDimension>& dims,
                                bool has_members) {
  // §37.17 detail 6: the mirror of VpiVariableLeftRange.
  return VpiRangeRightRange(LeftmostVariableRange(dims, has_members));
}

VpiHandle VpiSelectSingleIndex(
    const std::vector<VpiHandle>& indices_inner_to_outer) {
  // §37.17 detail 5: the index of a var select in a one-dimensional array is its
  // single innermost index.
  if (indices_inner_to_outer.empty()) return nullptr;
  return indices_inner_to_outer.front();
}

std::vector<VpiHandle> VpiSelectIndicesOutward(
    const std::vector<VpiHandle>& indices_inner_to_outer) {
  // §37.17 details 5, 13, and 18: the iteration runs from the innermost index
  // outward, which is the order the inputs are already in.
  return indices_inner_to_outer;
}

int VpiVariableSize(const VpiVariableSizeQuery& query) {
  // §37.17 details 9 and 10: vpiSize depends on the kind of variable.
  if (VpiIsArrayVarType(query.var_type)) {
    return query.array_element_count;  // variable array -> element count
  }
  if (VpiIsLogicVarType(query.var_type)) {
    return query.bit_width;  // logic var (reg) -> size in bits
  }
  switch (query.var_type) {
    case vpiByteVar:
    case vpiShortIntVar:
    case vpiIntVar:
    case vpiLongIntVar:
    case vpiIntegerVar:
    case vpiTimeVar:
    case vpiBitVar:
    case vpiEnumVar:
    case vpiPackedArrayVar:
      return query.bit_width;  // integer-typed/packed/enum -> size in bits
    case vpiStructVar:
    case vpiUnionVar:
      // packed -> size in bits; unpacked -> number of fields
      return query.packed ? query.bit_width : query.field_count;
    case vpiStringVar:
      return query.string_length;  // current character count
    case vpiVarBit:
      return 1;  // a var bit is one bit
    case vpiVarSelect:
      return query.bit_width;  // bits in the (packed) var select
    default:
      return 0;  // behavior of vpiSize not defined for other variables
  }
}

int VpiFunctionSize(bool is_void_function, bool return_size_defined,
                    int return_var_size) {
  // §37.41 detail 12: a void function has no return value, so its size is 0.
  // Otherwise, when the vpiReturn variable's size is defined and determinable
  // without evaluating the function, the function's size is that variable's size
  // (§37.17 detail 9 is what defines the variable's size). Every remaining case is
  // undefined; report 0, the same not-defined value VpiVariableSize uses.
  if (is_void_function) return 0;
  if (return_size_defined) return return_var_size;
  return 0;
}

bool VpiVariableHasValueProperty(int var_type, bool vpi_vector) {
  // §37.17 detail 11: array, class, and virtual-interface variables have no
  // value property, and neither does an unpacked struct/union (vpiVector FALSE).
  if (VpiIsArrayVarType(var_type) || var_type == vpiClassVar ||
      var_type == vpiVirtualInterfaceVar) {
    return false;
  }
  if ((var_type == vpiStructVar || var_type == vpiUnionVar) && !vpi_vector) {
    return false;
  }
  return true;
}

bool VpiBitIteratorApplies(int var_type, bool packed) {
  // §37.17 detail 12: vpiBit applies to logic, bit, packed struct, packed union,
  // and packed array variables only.
  if (VpiIsLogicVarType(var_type) || var_type == vpiBitVar ||
      var_type == vpiPackedArrayVar) {
    return true;
  }
  if (var_type == vpiStructVar || var_type == vpiUnionVar) {
    return packed;
  }
  return false;
}

bool VpiIsRandTypeValue(int value) {
  // §37.17 details 15 and 22: the three randomization types.
  return value == vpiRand || value == vpiRandC || value == vpiNotRand;
}

bool VpiIsRandomized(bool active_for_randomization) {
  // §37.17 detail 16: vpiIsRandomized is exactly that activeness.
  return active_for_randomization;
}

bool VpiIsArrayTypeValue(int value) {
  // §37.17 detail 21: the four array-type values.
  return value == vpiStaticArray || value == vpiDynamicArray ||
         value == vpiAssocArray || value == vpiQueueArray;
}

bool VpiVariableScalar(const VpiScalarVectorQuery& query) {
  // §37.17 detail 20: a bit/logic var with no packed dimension and a var bit are
  // scalars; an enum var defers to its base typespec; an array var defers to an
  // element; every other variable kind is not a scalar.
  if (VpiIsLogicVarType(query.var_type) || query.var_type == vpiBitVar) {
    return !query.has_packed_dimension;
  }
  if (query.var_type == vpiVarBit) return true;
  if (query.var_type == vpiEnumVar) return query.base_is_scalar;
  if (VpiIsArrayVarType(query.var_type)) return query.element_is_scalar;
  return false;
}

bool VpiVariableVector(const VpiScalarVectorQuery& query) {
  // §37.17 detail 20: a packed bit/logic var, a packed struct/union/array var,
  // and the integer-typed vars are vectors; an enum var defers to its base
  // typespec; an array var defers to an element; everything else is not a vector.
  if (VpiIsLogicVarType(query.var_type) || query.var_type == vpiBitVar) {
    return query.has_packed_dimension;
  }
  if (query.var_type == vpiPackedArrayVar) return true;
  if (query.var_type == vpiStructVar || query.var_type == vpiUnionVar) {
    return query.packed;
  }
  if (query.var_type == vpiVarBit) return false;
  if (query.var_type == vpiEnumVar) return query.base_is_vector;
  switch (query.var_type) {
    case vpiIntegerVar:
    case vpiTimeVar:
    case vpiShortIntVar:
    case vpiIntVar:
    case vpiLongIntVar:
    case vpiByteVar:
      return true;
    default:
      break;
  }
  if (VpiIsArrayVarType(query.var_type)) return query.element_is_vector;
  return false;
}

int VpiVariableVisibility(bool is_class_member, int declared_visibility) {
  // §37.17 detail 24: a non-class-member variable, and a class member that is
  // neither local nor protected, reports vpiPublicVis.
  if (!is_class_member) return vpiPublicVis;
  if (declared_visibility == vpiLocalVis ||
      declared_visibility == vpiProtectedVis) {
    return declared_visibility;
  }
  return vpiPublicVis;
}

int VpiTaskFuncVisibility(bool is_class_member, int declared_visibility) {
  // §37.41 detail 4: a task or function that is not a class member, and a class
  // member (method) that is neither local nor protected, reports vpiPublicVis;
  // a local or protected method reports its declared visibility.
  if (!is_class_member) return vpiPublicVis;
  if (declared_visibility == vpiLocalVis ||
      declared_visibility == vpiProtectedVis) {
    return declared_visibility;
  }
  return vpiPublicVis;
}

std::string VpiClassMemberFullName(bool is_static, std::string_view scope_path,
                                   std::string_view class_defn,
                                   std::string_view member) {
  // §37.17 detail 25: a non-static class data member has no full name; a static
  // member's full name routes through the "class defn" with "::", e.g.
  // "top.Packet::Id".
  if (!is_static) return std::string();
  std::string result;
  if (!scope_path.empty()) {
    result += std::string(scope_path) + ".";
  }
  result += std::string(class_defn) + "::" + std::string(member);
  return result;
}

VpiHandle VpiVariableParent(const std::vector<VpiParentPrefix>& prefixes) {
  // §37.17 detail 26: scan the prefixes rightmost to leftmost and return the
  // first one that qualifies; NULL when none does.
  for (const auto& prefix : prefixes) {
    if (prefix.qualifies) return prefix.handle;
  }
  return nullptr;
}

VpiHandle VpiLargestContainingArray(
    const std::vector<VpiHandle>& nested_innermost_first) {
  // §37.17 detail 26: the largest containing array is the outermost of the
  // nested array prefixes (the last entry when given innermost first).
  if (nested_innermost_first.empty()) return nullptr;
  return nested_innermost_first.back();
}

bool VpiConstantSelect(const VpiConstantSelectQuery& query) {
  // §37.17 detail 27: a static-lifetime variable with no parent is a constant
  // select, as is a select whose indices are all elaboration-time constants and
  // whose elements are all struct/union members or static-bound array elements.
  if (query.has_static_lifetime && !query.has_parent) return true;
  return query.all_indices_constant && query.all_elements_static_members;
}

std::string VpiVariableName(const VpiVariableNameParts& parts) {
  // §37.17 detail 28: the leaf member and its own index/slice, no prefixes.
  return parts.member + parts.index_suffix;
}

std::string VpiVariableDecompile(const VpiVariableNameParts& parts) {
  // §37.17 detail 28: the struct/union/class-var prefixes joined to the member,
  // without the top-level scope.
  std::string result;
  for (const auto& prefix : parts.member_prefixes) {
    result += prefix + ".";
  }
  result += parts.member + parts.index_suffix;
  return result;
}

std::string VpiVariableFullName(const VpiVariableNameParts& parts) {
  // §37.17 detail 28: the top-level scope prefixed to the decompile form.
  std::string decompile = VpiVariableDecompile(parts);
  if (parts.top_scope.empty()) return decompile;
  return parts.top_scope + "." + decompile;
}

// ===========================================================================
// §37.25 Typespec (the typespec object model; range relations route through
// §37.22, and a member's expr role reuses §37.59's expr class).
// ===========================================================================

bool VpiIsTypespecType(int type) {
  // §37.25: every "... typespec" node of Figure 37.25 - the built-in scalar and
  // integer typespecs, the user-defined-type typespecs, the array/packed-array
  // typespecs, and (detail 11) an unresolved type parameter, which acts as a
  // typespec. Each numeric value is listed once; some Annex M spellings (e.g.
  // vpiChandleTypespec, vpiIntegerTypespec, vpiTimeTypespec, vpiRealTypespec)
  // share a value with a name already covered here.
  switch (type) {
    case vpiTypespec:
    case vpiTypeParameter:
    case vpiLongIntTypespec:
    case vpiShortIntTypespec:
    case vpiIntTypespec:
    case vpiShortRealTypespec:
    case vpiByteTypespec:
    case vpiClassTypespec:
    case vpiStringTypespec:
    case vpiEnumTypespec:
    case vpiStructTypespec:
    case vpiUnionTypespec:
    case vpiBitTypespec:
    case vpiLogicTypespec:
    case vpiPackedArrayTypespec:
    case vpiArrayTypespec:
    case vpiVoidTypespec:
    case vpiSequenceTypespec:
    case vpiPropertyTypespec:
    case vpiEventTypespec:
    case vpiInterfaceTypespec:
      return true;
    default:
      return false;
  }
}

const char* VpiTypespecName(int ts_type, bool denotes_user_typedef,
                            const char* typedef_name, const char* class_name) {
  // §37.25 detail 1: a class typespec reports the class name; otherwise a
  // user-defined typedef reports the typedef's name (possibly empty for an inline
  // field, detail 5); a built-in type reports NULL.
  if (ts_type == vpiClassTypespec) return class_name;
  if (denotes_user_typedef) return typedef_name;
  return nullptr;
}

VpiHandle VpiTypespecTypedefAlias(bool is_alias, VpiHandle aliased_typedef) {
  // §37.25 detail 1: only a typespec whose typedef aliases another typedef hands
  // back the aliased typedef; otherwise vpiTypedefAlias is NULL.
  return is_alias ? aliased_typedef : nullptr;
}

VpiHandle VpiTypespecIndexTypespec(bool is_assoc_array_typespec,
                                   bool wildcard_index, VpiHandle key_typespec) {
  // §37.25 detail 2: the index typespec exists only for an associative array, and
  // a wildcard index type has none.
  if (!is_assoc_array_typespec || wildcard_index) return nullptr;
  return key_typespec;
}

std::vector<VpiHandle> VpiTypespecMembers(
    int ts_type, const std::vector<VpiHandle>& members) {
  // §37.25 detail 3: only a struct or union typespec exposes typespec members.
  if (ts_type == vpiStructTypespec || ts_type == vpiUnionTypespec) {
    return members;
  }
  return {};
}

VpiHandle VpiTypespecMemberTypespec(VpiHandle member) {
  // §37.25 detail 3: the member's type is its typespec child.
  if (!member) return nullptr;
  for (auto* child : member->children) {
    if (VpiIsTypespecType(child->type)) return child;
  }
  return nullptr;
}

const char* VpiTypespecMemberName(VpiHandle member) {
  // §37.25 detail 4: a typespec member reports its own name.
  if (!member) return nullptr;
  return member->name.data();
}

VpiHandle VpiTypespecMemberDefaultExpr(VpiHandle member) {
  // §37.25 detail 7: a member's default value is reached as its expr child (an
  // object of the §37.59 expr class); a member without a default has none.
  if (!member) return nullptr;
  for (auto* child : member->children) {
    if (VpiIsExprType(child->type)) return child;
  }
  return nullptr;
}

VpiHandle VpiTypespecElemTypespec(bool has_ranges, VpiHandle element_typespec) {
  // §37.25 detail 8: unwinding the leftmost range yields the element typespec;
  // once no ranges remain there is nothing left to unwind, so it is NULL.
  return has_ranges ? element_typespec : nullptr;
}

std::vector<VpiRangeDesc> VpiTypespecRanges(
    const std::vector<VpiArrayDimension>& dims) {
  // §37.25 detail 10: one range per dimension, leftmost to rightmost, each routed
  // through §37.22 so a dynamic/queue/associative dimension becomes an empty
  // range. An implicit element range is not a declared dimension of the typespec.
  std::vector<VpiRangeDesc> ranges;
  for (const auto& dim : dims) {
    if (dim.implicit_element_range) continue;
    VpiRangeDesc range;
    range.empty = VpiDimensionRangeIsEmpty(dim.kind);
    range.left_expr = dim.left_expr;
    range.right_expr = dim.right_expr;
    range.size = dim.size;
    ranges.push_back(range);
  }
  return ranges;
}

// §37.25 detail 9: the typespec's leftmost declared dimension drives
// vpiLeftRange/vpiRightRange. With no declared dimension the range is empty, so
// both relations yield NULL.
static VpiRangeDesc LeftmostTypespecRange(
    const std::vector<VpiArrayDimension>& dims) {
  for (const auto& dim : dims) {
    if (dim.implicit_element_range) continue;
    VpiRangeDesc range;
    range.empty = VpiDimensionRangeIsEmpty(dim.kind);
    range.left_expr = dim.left_expr;
    range.right_expr = dim.right_expr;
    range.size = dim.size;
    return range;
  }
  VpiRangeDesc empty;
  empty.empty = true;
  return empty;
}

VpiHandle VpiTypespecLeftRange(const std::vector<VpiArrayDimension>& dims) {
  // §37.25 detail 9: defer to §37.22, which yields NULL for an empty leftmost
  // range.
  return VpiRangeLeftRange(LeftmostTypespecRange(dims));
}

VpiHandle VpiTypespecRightRange(const std::vector<VpiArrayDimension>& dims) {
  // §37.25 detail 9: the mirror of VpiTypespecLeftRange.
  return VpiRangeRightRange(LeftmostTypespecRange(dims));
}

VpiHandle VpiTypespecForTypeParameter(VpiHandle type_parameter,
                                      VpiHandle resolved_typespec) {
  // §37.25 detail 11: an unresolved type parameter acts as the typespec itself.
  return resolved_typespec ? resolved_typespec : type_parameter;
}

// ===========================================================================
// §37.26 Structures and unions.
// ===========================================================================

bool VpiIsStructOrUnionType(int type) {
  // §37.26 (figure): the structure/union object kinds - a struct or union
  // declared as a variable, and a struct or union declared as a net.
  return type == vpiStructVar || type == vpiUnionVar ||
         type == vpiStructNet || type == vpiUnionNet;
}

bool VpiIsEntireUnpackedStructOrUnion(int type, bool packed) {
  // §37.26 detail 1: the value-access restriction applies to an entire unpacked
  // structure or union. A packed aggregate has a single vector value and is
  // accessible, so the restriction is the struct/union kinds with vpiPacked
  // false.
  return VpiIsStructOrUnionType(type) && !packed;
}

// ===========================================================================
// §37.28 Parameter, spec param, def param, param assign.
// ===========================================================================

VpiHandle VpiTypeParameterTypespec(VpiHandle type_parameter) {
  // §37.28 detail 2: hand back the stored typespec verbatim. The detail asks for
  // the typespec the type parameter has at the end of elaboration "without
  // resolving typedef aliases", so we deliberately do not run §37.25/§37.30's
  // alias resolution here - the recorded typespec is returned as-is, even when it
  // is itself a typedef alias.
  if (!type_parameter || type_parameter->type != vpiTypeParameter) {
    return nullptr;
  }
  return type_parameter->param_typespec;
}

VpiHandle VpiParameterDefaultExpr(VpiHandle parameter) {
  // §37.28 detail 3: vpiExpr reaches the parameter's default - a value
  // parameter's default value expression, or a type parameter's default
  // typespec. Both are kept in the same designated slot.
  if (!parameter ||
      (parameter->type != vpiParameter &&
       parameter->type != vpiTypeParameter)) {
    return nullptr;
  }
  return parameter->param_default;
}

VpiHandle VpiParamAssignLhs(VpiHandle param_assign) {
  // §37.28 detail 4: vpiLhs reaches the overridden parameter - the value
  // parameter (vpiParameter) or type parameter (vpiTypeParameter) among the
  // param assign's children. The override target is a parameter-kind object, not
  // a child whose own type is literally vpiLhs, so the generic walk cannot find
  // it.
  if (!param_assign || param_assign->type != vpiParamAssign) return nullptr;
  for (auto* child : param_assign->children) {
    if (child->type == vpiParameter || child->type == vpiTypeParameter) {
      return child;
    }
  }
  return nullptr;
}

VpiHandle VpiParameterLeftRange(VpiHandle parameter) {
  // §37.28 detail 5: a value parameter declared without an explicit range
  // reports a null handle for vpiLeftRange; only an explicitly ranged parameter
  // reaches its left range-bound expression.
  if (!parameter || parameter->type != vpiParameter ||
      !parameter->explicit_param_range) {
    return nullptr;
  }
  return parameter->param_left_range;
}

VpiHandle VpiParameterRightRange(VpiHandle parameter) {
  // §37.28 detail 5: the mirror of VpiParameterLeftRange for vpiRightRange.
  if (!parameter || parameter->type != vpiParameter ||
      !parameter->explicit_param_range) {
    return nullptr;
  }
  return parameter->param_right_range;
}

// ===========================================================================
// §37.29 Virtual interface.
// ===========================================================================

bool VpiIsInterfaceExprType(int type) {
  // §37.29 (figure, "interface expr" group): the object kinds that may sit at
  // the far end of a virtual interface var's vpiExpr - an interface, a modport,
  // another virtual interface var, a ref obj, or a constant.
  return type == vpiInterface || type == vpiModport ||
         type == vpiVirtualInterfaceVar || type == vpiRefObj ||
         type == vpiConstant;
}

bool VpiInterfaceExprIsValid(VpiHandle expr) {
  // §37.29 detail 2: not every object of an interface-expr kind is a legal
  // interface expr. A ref obj qualifies only when it is a local declaration of
  // an interface or modport passed through a port - observable as its vpiActual
  // being an interface or a modport. A constant qualifies only when its
  // vpiConstType is vpiNullConst. An interface, a modport, or a virtual
  // interface var always qualifies.
  if (!expr) return false;
  switch (expr->type) {
    case vpiRefObj:
      return expr->actual && (expr->actual->type == vpiInterface ||
                              expr->actual->type == vpiModport);
    case vpiConstant:
      return expr->const_type == vpiNullConst;
    case vpiInterface:
    case vpiModport:
    case vpiVirtualInterfaceVar:
      return true;
    default:
      return false;
  }
}

VpiHandle VpiVirtualInterfaceExpr(VpiHandle var) {
  // §37.29 detail 1: vpiExpr of a virtual interface var reaches the interface
  // instance assigned to it in its declaration, if any; otherwise NULL. The
  // assignment is modeled as the first child that is a legal interface expr,
  // so a child of an interface-expr kind that fails the detail-2 constraint is
  // not an interface expr and is not handed back.
  if (!var || var->type != vpiVirtualInterfaceVar) return nullptr;
  for (auto* child : var->children) {
    if (VpiIsInterfaceExprType(child->type) && VpiInterfaceExprIsValid(child)) {
      return child;
    }
  }
  return nullptr;
}

// ===========================================================================
// §37.30 Interface typespec.
// ===========================================================================

const char* VpiInterfaceTypespecDefName(VpiHandle interface_typespec) {
  // §37.30 detail 1: a modport interface typespec reports the modport
  // identifier as its vpiDefName, and an interface interface typespec reports
  // the interface declaration's identifier. Either definition name is held on
  // the typespec, so it is handed back directly; a typespec with no recorded
  // definition name, or a handle of any other kind, yields NULL.
  if (!interface_typespec ||
      interface_typespec->type != vpiInterfaceTypespec) {
    return nullptr;
  }
  return interface_typespec->def_name.empty()
             ? nullptr
             : interface_typespec->def_name.c_str();
}

VpiHandle VpiInterfaceTypespecParent(VpiHandle interface_typespec) {
  // §37.30 detail 2: a modport interface typespec's vpiParent is the interface
  // typespec of the interface it belongs to; an interface interface typespec
  // has no parent, so it reports NULL even when some enclosing object exists.
  if (!interface_typespec ||
      interface_typespec->type != vpiInterfaceTypespec) {
    return nullptr;
  }
  return interface_typespec->is_modport ? interface_typespec->parent : nullptr;
}

// ===========================================================================
// §37.48 Clocking block.
// ===========================================================================

VpiHandle VpiClockingBlockPrefix(VpiHandle block) {
  // §37.48 detail 2: vpiPrefix of a clocking block is non-NULL exactly when the
  // clocking block names an expression immediately prefixed by a virtual
  // interface (for example "vif.cb"). That prefix - the virtual interface var -
  // is modeled as a virtual interface var child. A clocking block that is not so
  // prefixed has no such child, so the relation reports NULL. The generic walk
  // cannot serve this transition: vpiPrefix and vpiVirtualInterfaceVar are
  // different type tags, so the prefix child is only found here.
  if (!block || block->type != vpiClockingBlock) return nullptr;
  for (auto* child : block->children) {
    if (child->type == vpiVirtualInterfaceVar) return child;
  }
  return nullptr;
}

VpiHandle VpiClockingBlockActual(VpiHandle block) {
  // §37.48 detail 3: vpiActual of a clocking block reaches the concrete clocking
  // block selected through its virtual interface prefix, held on the designated
  // actual pointer. When the prefix is a virtual interface that has no value at
  // the current simulation time - its own vpiActual being NULL, exactly as a
  // virtual interface var is left uninitialized in §37.29 - the clocking block's
  // vpiActual is NULL as well, regardless of any resolved actual.
  if (!block || block->type != vpiClockingBlock) return nullptr;
  VpiHandle prefix = VpiClockingBlockPrefix(block);
  if (prefix && prefix->actual == nullptr) return nullptr;
  return block->actual;
}

bool VpiIsClockingIODeclExprType(int type) {
  // §37.48 (figure, clocking io decl -> nets / variables / ref obj): the object
  // kinds a clocking io decl's vpiExpr relation may reach. As in §37.13's io
  // decl, the named target is a net, a variable (a logic var shares vpiReg's
  // code), or a ref obj.
  return type == vpiRefObj || type == kVpiNet || type == kVpiReg ||
         type == vpiVariables || VpiIsLogicVarType(type);
}

VpiHandle VpiClockingIODeclExpr(VpiHandle io_decl) {
  // §37.48 detail 4: vpiExpr of a clocking io decl reaches the expression or ref
  // obj the io decl names. For "enable = top.mem1.enable" the io decl "enable"
  // reaches a handle to the ref obj "top.mem1.enable". The named object is
  // modeled as the first child of a net / variable / ref obj kind; the io decl's
  // other children (its input/output skews) are not the named expression. The
  // generic walk cannot serve this transition because vpiExpr and the named
  // object carry different type tags.
  if (!io_decl || io_decl->type != vpiClockingIODecl) return nullptr;
  for (auto* child : io_decl->children) {
    if (VpiIsClockingIODeclExprType(child->type)) return child;
  }
  return nullptr;
}

// ===========================================================================
// §37.13 IO declaration.
// ===========================================================================

bool VpiIsIoDeclExprType(int type) {
  // §37.13: the object kinds the io decl's vpiExpr relation draws to - the named
  // ref obj / interface tf decl / virtual interface var target boxes plus the
  // nets and variables groupings (a logic var shares vpiReg's code).
  return type == vpiRefObj || type == vpiInterfaceTfDecl ||
         type == vpiVirtualInterfaceVar || type == kVpiNet || type == kVpiReg;
}

int VpiIoDeclExprType(bool passed_by_reference, bool is_interface_or_modport,
                      bool is_virtual_interface, int default_expr_type) {
  // §37.13 detail 2: a virtual-interface io decl resolves to its virtual
  // interface var; an io decl passed by reference, or one that is an interface
  // or a modport, resolves to a ref obj. Anything else keeps the directly
  // connected expression kind the caller already knows.
  if (is_virtual_interface) return vpiVirtualInterfaceVar;
  if (passed_by_reference || is_interface_or_modport) return vpiRefObj;
  return default_expr_type;
}

int VpiIoDeclDirection(int declared_direction, bool passed_by_reference,
                       bool expr_is_ref_obj_to_interface_or_modport,
                       bool expr_is_virtual_interface_var) {
  // §37.13 detail 3 first: an io decl whose vpiExpr denotes an interface/modport
  // (through a ref obj) or a virtual interface var has no defined direction.
  if (expr_is_ref_obj_to_interface_or_modport ||
      expr_is_virtual_interface_var) {
    return vpiNoDirection;
  }
  // §37.13 detail 1: a port or argument passed by reference reports vpiRef.
  if (passed_by_reference) return vpiRef;
  return declared_direction;
}

VpiHandle VpiIoDeclExpr(VpiHandle io_decl) {
  // §37.13 detail 2: vpiExpr of an io decl reaches a single designated
  // connection whose own type is an expr-target kind rather than vpiExpr, so the
  // first such child is the relation's target.
  if (!io_decl || io_decl->type != vpiIODecl) return nullptr;
  for (auto* child : io_decl->children) {
    if (VpiIsIoDeclExprType(child->type)) return child;
  }
  return nullptr;
}

std::vector<VpiRangeDesc> VpiIoDeclRanges(
    const std::vector<VpiArrayDimension>& dims) {
  // §37.13 detail 4: the io decl's vpiRange iteration is the same as for its
  // corresponding typespec (§37.25).
  return VpiTypespecRanges(dims);
}

VpiHandle VpiIoDeclLeftRange(const std::vector<VpiArrayDimension>& dims) {
  // §37.13 detail 4: vpiLeftRange is the corresponding typespec's vpiLeftRange.
  return VpiTypespecLeftRange(dims);
}

VpiHandle VpiIoDeclRightRange(const std::vector<VpiArrayDimension>& dims) {
  // §37.13 detail 4: vpiRightRange is the corresponding typespec's vpiRightRange.
  return VpiTypespecRightRange(dims);
}

// ===========================================================================
// §37.14 Ports and §37.15 Reference objects.
// ===========================================================================

bool VpiIsValidPortType(int port_type) {
  // §37.14 detail 1: a port's vpiPortType is one of exactly these three values.
  return port_type == vpiPort || port_type == vpiInterfacePort ||
         port_type == vpiModportPort;
}

int VpiPortTypeFromFormal(bool formal_is_interface, bool formal_is_modport) {
  // §37.14 detail 1: the port type follows the formal. A modport formal makes a
  // modport port, an interface formal an interface port, and anything else an
  // ordinary port. The actual the port connects to is never consulted.
  if (formal_is_modport) return vpiModportPort;
  if (formal_is_interface) return vpiInterfacePort;
  return vpiPort;
}

bool VpiPortDelaysApplicable(int port_type) {
  // §37.14 detail 2: the delay routines do not apply to an interface port.
  return port_type != vpiInterfacePort;
}

VpiHandle VpiHighConn(VpiHandle obj) {
  // §37.14 details 3 and 10 (shared with §37.15): the higher connection, or NULL
  // when the instance has no connection to the port. A null pointer already
  // encodes "no connection", so it is handed straight back.
  if (!obj) return nullptr;
  return obj->high_conn;
}

VpiHandle VpiLowConn(VpiHandle obj) {
  // §37.14 details 4 and 10 (shared with §37.15): the lower connection. A null
  // port carries no low connection, so its stored pointer is NULL.
  if (!obj) return nullptr;
  if (obj->null_port) return nullptr;
  return obj->low_conn;
}

bool VpiPortLowConnSatisfiesInterfaceRule(VpiHandle port) {
  // §37.14 detail 5: an interface port's lowConn must always be a ref obj
  // (§37.15). For any other port type the rule does not constrain the lowConn.
  if (!port || port->port_type != vpiInterfacePort) return true;
  return port->low_conn != nullptr && port->low_conn->type == vpiRefObj;
}

bool VpiPortScalar(int port_width) {
  // §37.14 detail 6: a port is scalar when it is exactly one bit wide. This
  // reflects the port itself, not whatever is connected to it.
  return port_width == 1;
}

bool VpiPortVector(int port_width) {
  // §37.14 detail 6: a port is a vector when it is more than one bit wide.
  return port_width > 1;
}

bool VpiPortIndexAndNameApply(int type) {
  // §37.14 detail 7: vpiPortIndex and vpiName apply to a whole port but not to a
  // port bit.
  return type != vpiPortBit;
}

const char* VpiPortName(bool explicitly_named, const char* explicit_name,
                        const char* inferred_name) {
  // §37.14 detail 8: an explicitly named port returns its explicit name; failing
  // that, an inferred name is returned if one exists; otherwise NULL.
  if (explicitly_named && explicit_name && explicit_name[0] != '\0') {
    return explicit_name;
  }
  if (inferred_name && inferred_name[0] != '\0') return inferred_name;
  return nullptr;
}

int VpiPortSize(bool is_null_port, int port_width) {
  // §37.14 detail 11: a null port has size 0; otherwise the size is the port's
  // bit width.
  return is_null_port ? 0 : port_width;
}

int VpiRefObjGeneric(bool refers_to_interface, bool is_generic_interface) {
  // §37.15 detail 5: a ref obj that refers to an interface reports whether that
  // interface is generic; any other ref obj reports vpiUndefined.
  if (!refers_to_interface) return vpiUndefined;
  return is_generic_interface ? 1 : 0;
}

// §37.15 detail 6: the actual kinds whose definition/modport name a ref obj's
// vpiDefName reports - an interface, an interface array, or a modport.
static bool VpiRefObjActualIsInterfaceOrModport(int actual_type) {
  return actual_type == vpiInterface || actual_type == vpiInterfaceArray ||
         actual_type == vpiModport;
}

const char* VpiRefObjDefName(VpiHandle ref_obj) {
  // §37.15 detail 6: when the ref obj's actual is an interface or modport, its
  // definition name (or the modport name) is reported; otherwise there is none.
  if (!ref_obj || !ref_obj->actual) return nullptr;
  if (!VpiRefObjActualIsInterfaceOrModport(ref_obj->actual->type)) {
    return nullptr;
  }
  return ref_obj->actual->name.data();
}

// §37.15 detail 7: the actual kinds that carry a typespec - a net, a variable,
// or a part select. A ref obj bound to any of these exposes vpiTypespec; bound
// to anything else (an interface, modport, named event, ...) it does not.
static bool VpiRefObjActualHasTypespec(int actual_type) {
  switch (actual_type) {
    case vpiNet:        // == kVpiNet, the net family head
    case vpiStructNet:
    case vpiUnionNet:
    case vpiEnumNet:
    case vpiIntegerNet:
    case vpiTimeNet:
    case vpiBitNet:
    case vpiPackedArrayNet:
    case vpiReg:        // == vpiLogicVar, the variable family head
    case vpiIntegerVar:
    case vpiRealVar:
    case vpiIntVar:
    case vpiBitVar:
    case vpiPartSelect:
      return true;
    default:
      return false;
  }
}

VpiHandle VpiRefObjTypespec(VpiHandle ref_obj) {
  // §37.15 detail 7: NULL unless the ref obj's actual is a net, variable, or part
  // select; in that case the ref obj's own typespec child is returned.
  if (!ref_obj || !ref_obj->actual) return nullptr;
  if (!VpiRefObjActualHasTypespec(ref_obj->actual->type)) return nullptr;
  for (auto* child : ref_obj->children) {
    if (child->type == vpiTypespec) return child;
  }
  return nullptr;
}

// ===========================================================================
// §37.16 Nets.
// ===========================================================================

// §37.16: the net object kinds the simulator's data type can hold. An
// integral-typed net is one whose value is a packed vector of bits (see 6.11.1);
// enum, logic, and bit nets are handled separately by the scalar/vector rules.
static bool VpiIsIntegralTypedNet(int net_type) {
  switch (net_type) {
    case vpiIntegerNet:
    case vpiTimeNet:
    case vpiByteNet:
    case vpiShortIntNet:
    case vpiIntNet:
    case vpiLongIntNet:
    case vpiPackedArrayNet:
      return true;
    default:
      return false;
  }
}

bool VpiIsArrayNet(int unpacked_range_count) {
  // §37.16 detail 1: one or more unpacked ranges makes a net an array net.
  return unpacked_range_count >= 1;
}

bool VpiIsPackedArrayNet(int net_type, int explicit_packed_range_count) {
  // §37.16 detail 1: a packed struct/union net or an enum net becomes a packed
  // array net when it carries at least one explicit packed range.
  if (explicit_packed_range_count < 1) return false;
  return net_type == vpiStructNet || net_type == vpiUnionNet ||
         net_type == vpiEnumNet;
}

bool VpiNetIsArrayMember(VpiHandle net) {
  // §37.16 detail 2: a net is an array member when its vpiParent prefix is an
  // array net.
  return net != nullptr && net->parent != nullptr &&
         net->parent->type == vpiNetArray;
}

bool VpiNetIsPackedArrayMember(VpiHandle net) {
  // §37.16 detail 2: vpiPackedArrayMember is TRUE for a packed struct/union net,
  // an enum net, or a packed array net whose vpiParent prefix is a packed array
  // net.
  if (!net || !net->parent || net->parent->type != vpiPackedArrayNet) {
    return false;
  }
  switch (net->type) {
    case vpiStructNet:
    case vpiUnionNet:
    case vpiEnumNet:
    case vpiPackedArrayNet:
      return true;
    default:
      return false;
  }
}

bool VpiNetBitIteratorApplies(int net_type) {
  // §37.16 detail 3: a logic net or bit net always exposes its net bits, whether
  // or not the vector was expanded.
  return net_type == vpiNet || net_type == vpiBitNet;
}

bool VpiNetTerminalAccessAllowed(bool is_scalar_net_or_bit_select) {
  // §37.16 detail 5: continuous assignments and primitive terminals are reachable
  // only from a scalar net or a bit-select.
  return is_scalar_net_or_bit_select;
}

VpiPortGranularity VpiPortsReferenceGranularity(int ref_type) {
  // §37.16 detail 6: a net bit reference selects the matching port bits; an
  // entire net or array net reference selects a handle to the whole port.
  if (ref_type == vpiNetBit) return VpiPortGranularity::kPortBits;
  return VpiPortGranularity::kEntirePort;
}

VpiPortGranularity VpiPortInstReferenceGranularity(
    bool ref_is_bit_or_scalar, bool ref_is_entire_net_or_array,
    bool highconn_bit_index_undeterminable) {
  // §37.16 detail 7: an entire net or array net reference always selects the
  // whole port. A bit or scalar reference selects the matching port bits or
  // scalar ports, except when the highconn is a complex expression whose bit
  // index cannot be determined - then the whole port is selected instead.
  if (ref_is_entire_net_or_array) return VpiPortGranularity::kEntirePort;
  if (ref_is_bit_or_scalar) {
    return highconn_bit_index_undeterminable ? VpiPortGranularity::kEntirePort
                                             : VpiPortGranularity::kPortBits;
  }
  return VpiPortGranularity::kEntirePort;
}

bool VpiPortInstReferenceQualifies(bool connected_to_any_port_bit) {
  // §37.16 detail 8: a reference inside the highconn that is connected to none of
  // the port's bits does not qualify as a member of the iteration.
  return connected_to_any_port_bit;
}

int VpiNetLineNo(bool implicit, int declared_line) {
  // §37.16 detail 9: an implicit net has no declaration line, so vpiLineNo is 0.
  return implicit ? 0 : declared_line;
}

bool VpiHasLocationProperties(int type) {
  // §37.3.3: vpiLineNo and vpiFile apply to every object that maps to source
  // text. The exceptions are object kinds that have no single source line or
  // file; for those the location properties are not valid queries.
  switch (type) {
    case vpiCallback:
    case vpiDelayTerm:
    case vpiDelayDevice:
    case vpiInterModPath:
    case vpiIterator:
    case vpiTimeQueue:
    case vpiGenScopeArray:
    case vpiGenScope:
      return false;
    default:
      return true;
  }
}

VpiHandle VpiNetBitIndex(const std::vector<VpiHandle>& indices_inner_to_outer) {
  // §37.16 detail 10: the bit index of a net bit is its single innermost index.
  if (indices_inner_to_outer.empty()) return nullptr;
  return indices_inner_to_outer.front();
}

std::vector<VpiHandle> VpiNetBitIndicesOutward(
    const std::vector<VpiHandle>& indices_inner_to_outer) {
  // §37.16 detail 10: a multidimensional net array bit-select iterates from the
  // net bit's index outward, the order the inputs already carry.
  return indices_inner_to_outer;
}

int VpiNetNettypeValue(bool is_part_of_nettype_net) {
  // §37.16 detail 11: a select of a nettype net reports vpiNettypeNetSelect; a
  // net not declared with a nettype reports vpiNettypeNet.
  return is_part_of_nettype_net ? vpiNettypeNetSelect : vpiNettypeNet;
}

bool VpiNetDriverIterationSupported(int nettype_value) {
  // §37.16 detail 11: driver iteration is unsupported on a vpiNettypeNetSelect.
  return nettype_value != vpiNettypeNetSelect;
}

int VpiInterconnectNetType() {
  // §37.16 detail 12: an interconnect net or interconnect net select reports
  // vpiInterconnect.
  return vpiInterconnect;
}

int VpiInterconnectResolvedNetType(int simulated_resolved_type) {
  // §37.16 detail 12: a simulated interconnect net resolves to the type of the
  // simulated net (see 23.3.3.7).
  return simulated_resolved_type;
}

VpiHandle VpiNetTypespec(VpiHandle net) {
  // §37.16 detail 13: an interconnect array has no typespec; any other net hands
  // back its first typespec child.
  if (!net || net->type == vpiInterconnectArray) return nullptr;
  for (auto* child : net->children) {
    if (child->type == vpiTypespec) return child;
  }
  return nullptr;
}

bool VpiNetBitExpanded(VpiHandle net_bit) {
  // §37.16 detail 21: vpiExpanded on a net bit reports the parent net's value. A
  // scalared net (and the default) is expanded; a vectored net is not.
  if (!net_bit || !net_bit->parent) return true;
  return !net_bit->parent->is_vectored;
}

bool VpiNetConstantSelect(bool has_parent, bool all_indices_constant,
                          bool all_elements_static_members) {
  // §37.16 detail 23: a net or net bit with no parent is a constant select, as is
  // a select whose indices are all elaboration-time constants and whose elements
  // are all struct/union net members or static-bound array elements.
  if (!has_parent) return true;
  return all_indices_constant && all_elements_static_members;
}

int VpiNetSize(const VpiNetSizeQuery& query) {
  // §37.16 detail 24: vpiSize depends on the kind of net.
  switch (query.net_type) {
    case vpiInterconnectArray:
      return query.interconnect_array_count;
    case vpiInterconnectNet:
      return query.connected_net_size;  // the connected net's size
    case vpiNetArray:
      return query.array_element_count;  // number of nets in the array
    case vpiNetBit:
      return 1;
    case vpiStructNet:
    case vpiUnionNet:
      // packed -> integral, size in bits; unpacked -> number of members
      return query.packed ? query.bit_width : query.member_count;
    default:
      break;
  }
  if (VpiIsIntegralTypedNet(query.net_type) || query.net_type == vpiNet ||
      query.net_type == vpiBitNet || query.net_type == vpiEnumNet) {
    return query.bit_width;  // net of an integral data type -> size in bits
  }
  return 0;  // vpiSize not defined for any other net
}

std::vector<VpiHandle> VpiNetIndicesOutward(
    bool is_array_member, const std::vector<VpiHandle>& indices_inner_to_outer) {
  // §37.16 detail 25: only an element of an array net has an index iteration; it
  // runs from the net's own index outward. A net that is not an array element
  // yields no indices.
  if (!is_array_member) return {};
  return indices_inner_to_outer;
}

std::vector<VpiRangeDesc> VpiNetRanges(
    const std::vector<VpiArrayDimension>& dims) {
  // §37.16 detail 26 (woven with §37.22): one range per declared dimension, in
  // declaration order. Each dimension routes through §37.22's empty-range rule;
  // the implicit element ranges of a packed struct/union element are dropped
  // (detail 1).
  std::vector<VpiRangeDesc> ranges;
  for (const auto& dim : dims) {
    if (dim.implicit_element_range) continue;
    VpiRangeDesc range;
    range.empty = VpiDimensionRangeIsEmpty(dim.kind);
    range.left_expr = dim.left_expr;
    range.right_expr = dim.right_expr;
    range.size = dim.size;
    ranges.push_back(range);
  }
  return ranges;
}

// §37.16 detail 26: the §37.22 range for a net's leftmost packed dimension, the
// one vpiLeftRange/vpiRightRange report. Returns an empty range (so both
// relations yield NULL) when the net has no dimensions.
static VpiRangeDesc LeftmostNetRange(
    const std::vector<VpiArrayDimension>& dims) {
  std::vector<VpiRangeDesc> ranges = VpiNetRanges(dims);
  if (ranges.empty()) {
    VpiRangeDesc empty;
    empty.empty = true;
    return empty;
  }
  return ranges.front();
}

VpiHandle VpiNetLeftRange(const std::vector<VpiArrayDimension>& dims) {
  // §37.16 detail 26: defer to §37.22's vpiLeftRange.
  return VpiRangeLeftRange(LeftmostNetRange(dims));
}

VpiHandle VpiNetRightRange(const std::vector<VpiArrayDimension>& dims) {
  // §37.16 detail 26: the mirror of VpiNetLeftRange.
  return VpiRangeRightRange(LeftmostNetRange(dims));
}

bool VpiNetScalar(const VpiNetScalarVectorQuery& query) {
  // §37.16 detail 28: a bit/logic net with no packed dimension and a net bit are
  // scalars; an enum net defers to its base typespec; an array net defers to an
  // element; every other net is not a scalar.
  if (query.net_type == vpiNet || query.net_type == vpiBitNet) {
    return !query.has_packed_dimension;
  }
  if (query.net_type == vpiNetBit) return true;
  if (query.net_type == vpiEnumNet) return query.base_is_scalar;
  if (query.net_type == vpiNetArray) return query.element_is_scalar;
  return false;
}

bool VpiNetVector(const VpiNetScalarVectorQuery& query) {
  // §37.16 detail 28: a bit/logic net with a packed dimension, the integral-typed
  // nets, and a packed struct/union net are vectors; an enum net defers to its
  // base typespec; an array net defers to an element; every other net is not a
  // vector.
  if (query.net_type == vpiNet || query.net_type == vpiBitNet) {
    return query.has_packed_dimension;
  }
  if (query.net_type == vpiNetBit) return false;
  if (query.net_type == vpiEnumNet) return query.base_is_vector;
  if (query.net_type == vpiStructNet || query.net_type == vpiUnionNet) {
    return query.packed;
  }
  if (query.net_type == vpiNetArray) return query.element_is_vector;
  return VpiIsIntegralTypedNet(query.net_type);
}

bool VpiNetHasValueProperty(int net_type, bool packed_struct_union) {
  // §37.16 detail 30: array nets, unpacked struct/union nets, and interconnect
  // arrays have no value property; every other net does.
  if (net_type == vpiNetArray || net_type == vpiInterconnectArray) return false;
  if ((net_type == vpiStructNet || net_type == vpiUnionNet) &&
      !packed_struct_union) {
    return false;
  }
  return true;
}

VpiHandle VpiNetParent(const std::vector<VpiParentPrefix>& prefixes) {
  // §37.16 detail 31: scan the prefixes rightmost to leftmost and return the
  // first one that qualifies; NULL when none does.
  for (const auto& prefix : prefixes) {
    if (prefix.qualifies) return prefix.handle;
  }
  return nullptr;
}

bool VpiNetElementIteratorApplies(int net_type) {
  // §37.16 detail 32: vpiElement iterates only over a packed array net.
  return net_type == vpiPackedArrayNet;
}

std::vector<VpiHandle> VpiPackedArrayNetElements(VpiHandle packed_array_net) {
  // §37.16 detail 32: the subelements of a packed array net are its element
  // children, returned in declaration order. A net that is not a packed array
  // net has none.
  if (!packed_array_net ||
      !VpiNetElementIteratorApplies(packed_array_net->type)) {
    return {};
  }
  return packed_array_net->children;
}

bool VpiNetStructUnionMember(VpiHandle net) {
  // §37.16 detail 33: TRUE for a net or array net whose vpiParent is a struct or
  // union net; not defined for a net bit (whose vpiParent is a net), reported
  // FALSE.
  if (!net || net->type == vpiNetBit || !net->parent) return false;
  return net->parent->type == vpiStructNet || net->parent->type == vpiUnionNet;
}

std::string VpiNetName(const VpiVariableNameParts& parts) {
  // §37.16 detail 34: the leaf member with its own index/slice, no prefixes.
  return parts.member + parts.index_suffix;
}

std::string VpiNetDecompile(const VpiVariableNameParts& parts) {
  // §37.16 detail 34: the struct/union-net prefixes joined to the member (with
  // its index/slice), without the top-level scope.
  std::string result;
  for (const auto& prefix : parts.member_prefixes) {
    result += prefix + ".";
  }
  result += parts.member + parts.index_suffix;
  return result;
}

std::string VpiNetFullName(const VpiVariableNameParts& parts) {
  // §37.16 detail 34: the top-level scope prefixed to the decompile form.
  std::string decompile = VpiNetDecompile(parts);
  if (parts.top_scope.empty()) return decompile;
  return parts.top_scope + "." + decompile;
}

// ===========================================================================
// §37.24 Generic interconnect.
//
// The generic-interconnect data model draws an interconnect array and the
// interconnect nets it ultimately resolves to. The relations that step into an
// interconnect's subobjects - vpiElement (an array element or a net's array
// element) and vpiMember (a net's struct member) - are named for the relation,
// not for the kind of object reached, so the Iterate dispatcher recognizes them
// specially below.
// ===========================================================================

bool VpiIsInterconnectSubelementType(int type) {
  // §37.24 details 1 and 2: stepping into an interconnect reaches another
  // interconnect object - a nested interconnect array (a further dimension
  // level) or a leaf interconnect net.
  return type == vpiInterconnectArray || type == vpiInterconnectNet;
}

bool VpiIsInterconnectArrayDataTypespec(int typespec_type) {
  // §37.24 detail 1: vpiElement reaches an interconnect net's elements only when
  // the data type of the typespec it connects to is a packed or unpacked array.
  return typespec_type == vpiArrayTypespec ||
         typespec_type == vpiPackedArrayTypespec;
}

bool VpiIsInterconnectStructDataTypespec(int typespec_type) {
  // §37.24 detail 1: vpiMember reaches an interconnect net's members only when
  // the data type of the typespec it connects to is a packed or unpacked struct;
  // a union is likewise member-bearing and reached the same way.
  return typespec_type == vpiStructTypespec || typespec_type == vpiUnionTypespec;
}

int VpiInterconnectNetTypespecType(VpiHandle interconnect_net) {
  // §37.24 detail 1: an interconnect net's typespec is the typespec of the net
  // or nets it connects to (§37.16 detail 13 hands it back). Its data-type kind
  // selects whether vpiElement or vpiMember reaches the net's subobjects, so
  // report the kind of the net's typespec child; zero when it has none.
  if (!interconnect_net) return 0;
  for (auto* child : interconnect_net->children) {
    if (VpiIsTypespecType(child->type)) return child->type;
  }
  return 0;
}

// ===========================================================================
// §37.11 Instance arrays.
// ===========================================================================

bool VpiIsPrimitiveArrayType(int type) {
  // §37.11 (primitive-array diagram): a primitive array and the three concrete
  // forms drawn beneath it - gate, switch, and udp arrays.
  switch (type) {
    case vpiPrimitiveArray:
    case vpiGateArray:
    case vpiSwitchArray:
    case vpiUdpArray:
      return true;
    default:
      return false;
  }
}

bool VpiIsInstanceArrayType(int type) {
  // §37.11 (instance-array diagram): the module, interface, and program arrays
  // drawn beneath instance array, plus every primitive array (a primitive array
  // is itself a kind of instance array) and the instance-array supertype.
  switch (type) {
    case vpiInstanceArray:
    case vpiModuleArray:
    case vpiInterfaceArray:
    case vpiProgramArray:
      return true;
    default:
      return VpiIsPrimitiveArrayType(type);
  }
}

VpiHandle VpiInstanceArrayConnections(VpiHandle instance_array) {
  // §37.11 detail 1: the expr reached from an instance array is the operation
  // object listing the array's actual connections, modeled as the array's first
  // operation child. A null, non-instance-array, or childless handle has none.
  if (!instance_array) return nullptr;
  if (!VpiIsInstanceArrayType(instance_array->type)) return nullptr;
  for (auto* child : instance_array->children) {
    if (child->type == vpiOperation) return child;
  }
  return nullptr;
}

bool VpiInstanceArrayConnectionsIsListOp(VpiHandle expr) {
  // §37.11 detail 1: that expr shall be a vpiOperation whose vpiOpType is
  // vpiListOp.
  return expr && expr->type == vpiOperation && expr->op_type == vpiListOp;
}

std::vector<VpiRangeDesc> VpiInstanceArrayRanges(
    const std::vector<VpiArrayDimension>& dims) {
  // §37.11 detail 2: one range per declared dimension, beginning with the
  // leftmost range of the array declaration and iterating through the rightmost.
  // Each dimension routes through §37.22's empty-range rule.
  std::vector<VpiRangeDesc> ranges;
  for (const auto& dim : dims) {
    VpiRangeDesc range;
    range.empty = VpiDimensionRangeIsEmpty(dim.kind);
    range.left_expr = dim.left_expr;
    range.right_expr = dim.right_expr;
    range.size = dim.size;
    ranges.push_back(range);
  }
  return ranges;
}

// §37.11 detail 2: the §37.22 range for an instance array's leftmost dimension,
// the one vpiLeftRange/vpiRightRange report. An array with no dimensions yields
// an empty range, so both relations report NULL.
static VpiRangeDesc LeftmostInstanceArrayRange(
    const std::vector<VpiArrayDimension>& dims) {
  std::vector<VpiRangeDesc> ranges = VpiInstanceArrayRanges(dims);
  if (ranges.empty()) {
    VpiRangeDesc empty;
    empty.empty = true;
    return empty;
  }
  return ranges.front();
}

VpiHandle VpiInstanceArrayLeftRange(
    const std::vector<VpiArrayDimension>& dims) {
  // §37.11 detail 2: vpiLeftRange returns the bound of the leftmost dimension;
  // defer to §37.22's vpiLeftRange.
  return VpiRangeLeftRange(LeftmostInstanceArrayRange(dims));
}

VpiHandle VpiInstanceArrayRightRange(
    const std::vector<VpiArrayDimension>& dims) {
  // §37.11 detail 2: the mirror of VpiInstanceArrayLeftRange.
  return VpiRangeRightRange(LeftmostInstanceArrayRange(dims));
}

void VpiContext::Attach(SimContext& sim_ctx) {
  for (auto& [name, var] : sim_ctx.GetVariables()) {
    auto* obj = AllocObject();
    obj->type = kVpiReg;
    obj->name = name;
    obj->var = var;
    obj->size = static_cast<int>(var->value.width);
    object_map_[name] = obj;
  }
}

VpiHandle VpiContext::RegisterSystf(VpiSystfData* data) {
  if (!data) return nullptr;

  // §36.9.1: a user-defined system task or system function name shall begin
  // with a dollar sign. §38.37.1 sharpens this: the dollar sign shall be
  // followed by one or more characters that are legal in a SystemVerilog simple
  // identifier. Refuse a name that fails either part of the rule (a missing or
  // bare "$", or any illegal trailing character).
  if (!VpiSystfNameIsValid(data->tfname)) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "system task or function name must be '$' followed by one or more "
        "identifier characters";
    return nullptr;
  }

  // §36.9.1: the registration of system tasks shall occur prior to elaboration
  // or the resolution of references. Once elaboration has begun the window has
  // closed, so reject the registration.
  if (elaboration_started_) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "system task or function registration must precede elaboration";
    return nullptr;
  }

  systfs_.push_back(*data);

  // §38.37 Returns row: registration produces a handle to the callback
  // object standing in for this system task or system function.
  auto* systf_obj = AllocObject();
  systf_obj->type = kVpiCallback;
  systf_obj->index = static_cast<int>(systfs_.size() - 1);
  // §38.12: mark this callback as a system task/function so vpi_get_systf_info()
  // can tell it apart from a simulation callback and read back its record.
  systf_obj->is_systf = true;
  return systf_obj;
}

void VpiContext::GetSystfInfo(VpiHandle obj, VpiSystfData* systf_data_p) {
  // §38.12 / §38.1: the handle and the destination are both mandatory. With no
  // structure to fill, or no callback to read, there is nothing to report.
  if (obj == nullptr || systf_data_p == nullptr) return;

  // §38.12: obj must name a system task or system function callback. Other
  // objects (including simulation callbacks) carry no s_vpi_systf_data record.
  if (obj->type != kVpiCallback || !obj->is_systf) return;
  int idx = obj->index;
  if (idx < 0 || idx >= static_cast<int>(systfs_.size())) return;

  // §38.12: copy the stored registration into the application-owned structure.
  // The routine never allocates that memory; it only writes the fields.
  *systf_data_p = systfs_[idx];
}

void VpiContext::GetCbInfo(VpiHandle obj, VpiCbData* cb_data_p) {
  // §38.8: the destination structure is allocated by the application. With no
  // structure to fill, or no callback to read, there is nothing to report; the
  // routine never allocates that memory itself.
  if (obj == nullptr || cb_data_p == nullptr) return;

  // §38.8: obj must name a simulation-related callback. A system task/function
  // callback carries an s_vpi_systf_data record instead (read it through
  // vpi_get_systf_info), so it is not a valid argument here.
  if (obj->type != kVpiCallback || obj->is_systf) return;
  int idx = obj->index;
  if (idx < 0 || idx >= static_cast<int>(callbacks_.size())) return;

  // §38.8: report the callback's information by writing the stored s_cb_data
  // fields into the caller's structure.
  *cb_data_p = callbacks_[idx];
}

VpiHandle VpiContext::CreateTimeQueue() {
  // §38.13: a time queue object carries no further state of its own; its kind is
  // enough for GetTime() to know to report the next future event time.
  auto* obj = AllocObject();
  obj->type = kVpiTimeQueue;
  return obj;
}

void VpiContext::GetTime(VpiHandle obj, VpiTime* time_p) {
  // §38.13 / §38.1: the destination is mandatory and its memory belongs to the
  // application. With nowhere to write, there is nothing to do; the routine
  // never allocates the structure itself.
  if (time_p == nullptr) return;

  // §38.13: choose the time value and the unit it is expressed in. A time queue
  // object reports the scheduled time of the next future event; every other
  // query reports the current simulation time. Both a null handle and a time
  // queue object are read in the simulation time unit; a regular object is read
  // in its own timescale.
  uint64_t ticks = 0;
  bool use_sim_time_unit = (obj == nullptr);
  if (obj != nullptr && obj->type == kVpiTimeQueue) {
    ticks = scheduler_ ? scheduler_->NextEventTime().ticks : 0;
    use_sim_time_unit = true;
  } else {
    ticks = scheduler_ ? scheduler_->CurrentTime().ticks : 0;
  }

  // §38.13 (Figure 38-6): the caller's time_p->type selects the form of the
  // result. vpiScaledRealTime asks for a real scaled to the relevant time unit;
  // anything else (vpiSimTime) asks for the raw 64-bit count.
  if (time_p->type == kVpiScaledRealTime) {
    // §38.13: scale the simulation-time-unit count into the target unit - the
    // object's timescale, or the simulation time unit for a null handle or a
    // time queue object. The exponent difference is the power-of-ten conversion
    // between the two units.
    int target_unit = use_sim_time_unit ? sim_time_unit_ : obj->time_unit;
    double scale = std::pow(10.0, static_cast<double>(sim_time_unit_ - target_unit));
    time_p->real = static_cast<double>(ticks) * scale;
  } else {
    // §38.13 (Figure 38-6): vpiSimTime delivers the 64-bit simulation time split
    // into its high and low 32-bit halves.
    time_p->high = static_cast<uint32_t>(ticks >> 32);
    time_p->low = static_cast<uint32_t>(ticks & 0xFFFFFFFFu);
  }
}

namespace {

// §38.10: the four object categories that carry delays. Their legal
// no_of_delays values differ, so vpi_get_delays() classifies the object first.
bool VpiObjectIsPrimitive(int type) {
  return type == vpiGate || type == vpiSwitch || type == vpiUdp ||
         type == vpiPrimitive || type == vpiSeqPrim || type == vpiCombPrim;
}

// §38.10: whether `n` is a legal number of delays to request for an object of
// `type` that carries `available` stored delays. For a primitive the count is
// 2 or 3; for a module (path-delay) object 1, 2, 3, 6, or 12; for an
// intermodule path 2 or 3; for a timing check it must match the number of
// limits the check actually has. Any other object bears no delays.
bool VpiNoOfDelaysLegal(int type, int n, size_t available) {
  if (VpiObjectIsPrimitive(type)) return n == 2 || n == 3;
  if (type == vpiModPath)
    return n == 1 || n == 2 || n == 3 || n == 6 || n == 12;
  if (type == vpiInterModPath) return n == 2 || n == 3;
  if (type == vpiTchk) return n == static_cast<int>(available);
  return false;
}

// §38.10: write one delay value into a caller-supplied time entry. The form is
// dictated solely by the delay structure's time_type - the entry's own type
// field is ignored on input and overwritten with time_type. vpiScaledRealTime
// delivers a real; vpiSimTime delivers the value as a 64-bit count split across
// high/low; vpiSuppressTime asks for no time and leaves the value cleared.
void VpiWriteDelayValue(VpiTime* slot, int time_type, double value) {
  slot->type = time_type;
  slot->high = 0;
  slot->low = 0;
  slot->real = 0.0;
  if (time_type == vpiScaledRealTime) {
    slot->real = value;
  } else if (time_type == vpiSimTime) {
    auto ticks = static_cast<uint64_t>(value);
    slot->high = static_cast<uint32_t>(ticks >> 32);
    slot->low = static_cast<uint32_t>(ticks & 0xFFFFFFFFu);
  }
}

// §38.32: read one delay value out of a caller-supplied time entry, the inverse
// of VpiWriteDelayValue. The form is dictated by the delay structure's
// time_type: vpiScaledRealTime carries the value in the real field; vpiSimTime
// carries it as a 64-bit count split across high/low; vpiSuppressTime carries
// no time, so the value is zero.
double VpiReadDelayValue(const VpiTime& slot, int time_type) {
  if (time_type == vpiScaledRealTime) return slot.real;
  if (time_type == vpiSimTime) {
    uint64_t ticks = (static_cast<uint64_t>(slot.high) << 32) | slot.low;
    return static_cast<double>(ticks);
  }
  return 0.0;
}

}  // namespace

void VpiContext::GetDelays(VpiHandle obj, VpiDelay* delay_p) {
  // §38.10 / §38.1: the structure and its da array are application-allocated.
  // With nothing to fill, or no object to read delays from, there is nothing
  // to do; the routine never allocates anything itself.
  if (delay_p == nullptr || obj == nullptr) return;

  // §37.14 detail 2: the delay routines are not applicable to an interface port.
  // Treat such a request as an error (§38.2) and leave the caller's array alone.
  if (obj->type == vpiPort && !VpiPortDelaysApplicable(obj->port_type)) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_get_delays(): delays are not applicable to an interface port";
    return;
  }

  // §38.10: the legal values for the number of delays are fixed by the object's
  // category. A request that is not legal for this object is an error; record
  // it (§38.2) and leave the caller's array untouched.
  if (!VpiNoOfDelaysLegal(obj->type, delay_p->no_of_delays,
                          obj->delays.size())) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_get_delays(): the requested number of delays is not legal for "
        "this object";
    return;
  }

  if (delay_p->da == nullptr) return;

  const bool mtm = delay_p->mtm_flag != 0;
  const bool pulsere = delay_p->pulsere_flag != 0;
  const int tt = delay_p->time_type;

  // §38.10 (Table 38-2): each delay occupies a run of da entries selected by
  // mtm_flag and pulsere_flag, and the delays appear in source order. Walk the
  // delays in order, emitting each delay's run before moving to the next.
  int k = 0;
  for (int i = 0; i < delay_p->no_of_delays; ++i) {
    const VpiDelayInfo d = (static_cast<size_t>(i) < obj->delays.size())
                               ? obj->delays[i]
                               : VpiDelayInfo{};
    if (!mtm && !pulsere) {
      // Neither flag set: one entry, the plain delay.
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.delay);
    } else if (mtm && !pulsere) {
      // min:typ:max only: three entries, min then typ then max delay.
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.min_delay);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.typ_delay);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.max_delay);
    } else if (!mtm && pulsere) {
      // Pulse limits only: delay, reject limit, error limit.
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.delay);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.reject);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.error);
    } else {
      // Both flags: nine entries - min:typ:max of delay, then reject, then
      // error.
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.min_delay);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.typ_delay);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.max_delay);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.min_reject);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.typ_reject);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.max_reject);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.min_error);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.typ_error);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.max_error);
    }
  }
}

void VpiContext::PutDelays(VpiHandle obj, VpiDelay* delay_p) {
  // §38.32 / §38.1: the structure and its da array are application-allocated.
  // With no source values or no target object there is nothing to set; the
  // routine never allocates the caller's memory itself.
  if (delay_p == nullptr || obj == nullptr) return;

  // §37.14 detail 2: the delay routines do not apply to an interface port.
  // Treat such a request as an error (§38.2) and change nothing.
  if (obj->type == vpiPort && !VpiPortDelaysApplicable(obj->port_type)) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_delays(): delays are not applicable to an interface port";
    return;
  }

  // §38.32: the legal number of delays is fixed by the object's category, the
  // same classification vpi_get_delays() uses. A request that is not legal for
  // this object is an error; record it (§38.2) and set nothing.
  if (!VpiNoOfDelaysLegal(obj->type, delay_p->no_of_delays,
                          obj->delays.size())) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_delays(): the requested number of delays is not legal for "
        "this object";
    return;
  }

  if (delay_p->da == nullptr) return;

  const bool mtm = delay_p->mtm_flag != 0;
  const bool pulsere = delay_p->pulsere_flag != 0;
  const int tt = delay_p->time_type;

  // Ensure there is a stored slot for every delay being set, preserving any
  // values already present so the pulse limits survive a delay-only write
  // (§38.32: pulse limits retain their prior values when only the delay is
  // altered).
  if (obj->delays.size() < static_cast<size_t>(delay_p->no_of_delays))
    obj->delays.resize(delay_p->no_of_delays);

  // §38.32 (Table 38-4, == the vpi_get_delays() Table 38-2 layout): each delay
  // occupies a run of da entries selected by mtm_flag and pulsere_flag, and the
  // delays are taken in source order. Only the fields the flags select are
  // written; every other field of the stored delay is left untouched, so when
  // pulsere_flag is clear the reject/error limits keep the values they had.
  int k = 0;
  for (int i = 0; i < delay_p->no_of_delays; ++i) {
    VpiDelayInfo& d = obj->delays[i];
    if (!mtm && !pulsere) {
      // Neither flag set: one entry, the plain delay.
      d.delay = VpiReadDelayValue(delay_p->da[k++], tt);
    } else if (mtm && !pulsere) {
      // min:typ:max only: three entries, min then typ then max delay.
      d.min_delay = VpiReadDelayValue(delay_p->da[k++], tt);
      d.typ_delay = VpiReadDelayValue(delay_p->da[k++], tt);
      d.max_delay = VpiReadDelayValue(delay_p->da[k++], tt);
    } else if (!mtm && pulsere) {
      // Pulse limits only: delay, reject limit, error limit.
      d.delay = VpiReadDelayValue(delay_p->da[k++], tt);
      d.reject = VpiReadDelayValue(delay_p->da[k++], tt);
      d.error = VpiReadDelayValue(delay_p->da[k++], tt);
    } else {
      // Both flags: nine entries - min:typ:max of delay, then reject, then
      // error.
      d.min_delay = VpiReadDelayValue(delay_p->da[k++], tt);
      d.typ_delay = VpiReadDelayValue(delay_p->da[k++], tt);
      d.max_delay = VpiReadDelayValue(delay_p->da[k++], tt);
      d.min_reject = VpiReadDelayValue(delay_p->da[k++], tt);
      d.typ_reject = VpiReadDelayValue(delay_p->da[k++], tt);
      d.max_reject = VpiReadDelayValue(delay_p->da[k++], tt);
      d.min_error = VpiReadDelayValue(delay_p->da[k++], tt);
      d.typ_error = VpiReadDelayValue(delay_p->da[k++], tt);
      d.max_error = VpiReadDelayValue(delay_p->da[k++], tt);
    }
  }
}

void VpiContext::SeedSaveData(int id, const char* data, int len) {
  // §38.9 / §38.32: append bytes to the save/restart store for `id`. This
  // stands in for the production writer vpi_put_data(); it does not touch the
  // read cursor, so a subsequent first vpi_get_data() reads from offset zero.
  if (data == nullptr || len <= 0) return;
  std::vector<char>& bytes = save_data_[id];
  bytes.insert(bytes.end(), data, data + len);
}

int VpiContext::GetData(int id, char* data_loc, int num_of_bytes) {
  // §38.9: legal only from an application routine running for reason
  // cbStartOfRestart or cbEndOfRestart. Any other context is a failure, which
  // the routine reports by returning 0.
  if (current_callback_reason_ != kCbStartOfRestart &&
      current_callback_reason_ != kCbEndOfRestart) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_get_data() may only be called from a cbStartOfRestart or "
        "cbEndOfRestart application routine";
    return 0;
  }

  // §38.9: a null buffer, a non-positive request, or an id that was never saved
  // is a failure - return 0.
  auto it = save_data_.find(id);
  if (data_loc == nullptr || num_of_bytes <= 0 || it == save_data_.end()) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message = "vpi_get_data() could not retrieve saved data";
    return 0;
  }

  const std::vector<char>& bytes = it->second;
  std::size_t& cursor = save_data_cursor_[id];
  const std::size_t available =
      (cursor < bytes.size()) ? bytes.size() - cursor : 0;

  if (static_cast<std::size_t>(num_of_bytes) > available) {
    // §38.9: asking for more than remains is a warning. Hand back the bytes
    // that are left, zero-fill the rest of the buffer, advance the cursor past
    // what was delivered, and return the count actually retrieved.
    const int retrieved = static_cast<int>(available);
    for (int i = 0; i < retrieved; ++i) data_loc[i] = bytes[cursor + i];
    for (int i = retrieved; i < num_of_bytes; ++i) data_loc[i] = '\0';
    cursor += available;
    last_error_.state = kVpiWarning;
    last_error_.level = kVpiWarning;
    last_error_.message =
        "vpi_get_data() requested more data than were saved for this id";
    return retrieved;
  }

  // §38.9: the normal case (and the explicitly-acceptable case of asking for
  // fewer bytes than were saved). Copy the request and advance the cursor so a
  // later call resumes where this one stopped.
  for (int i = 0; i < num_of_bytes; ++i) data_loc[i] = bytes[cursor + i];
  cursor += static_cast<std::size_t>(num_of_bytes);
  return num_of_bytes;
}

int VpiContext::PutData(int id, const char* data_loc, int num_of_bytes) {
  // §38.31: legal only from an application routine running for reason
  // cbStartOfSave or cbEndOfSave. Any other context is an error, which the
  // routine reports by returning zero bytes written.
  if (current_callback_reason_ != kCbStartOfSave &&
      current_callback_reason_ != kCbEndOfSave) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_data() may only be called from a cbStartOfSave or "
        "cbEndOfSave application routine";
    return 0;
  }

  // §38.31: numOfBytes shall be greater than zero, and the source storage must
  // be supplied by the application. Either condition is a detected error, which
  // returns zero bytes written.
  if (data_loc == nullptr || num_of_bytes <= 0) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_data() requires a non-null source and a positive byte count";
    return 0;
  }

  // §38.31: append the bytes to the save/restart store for this id. There is no
  // limit on how many times an id is written and no ordering constraint across
  // ids; storing the bytes contiguously lets vpi_get_data() (§38.9) read them
  // back later in chunks of any size. The return value is the number of bytes
  // written.
  std::vector<char>& bytes = save_data_[id];
  bytes.insert(bytes.end(), data_loc, data_loc + num_of_bytes);
  return num_of_bytes;
}

namespace {

// §38.21: split a possibly hierarchical name into its dot-separated path
// components, outermost scope first. A simple name yields a single component.
std::vector<std::string_view> VpiNamePathComponents(std::string_view name) {
  std::vector<std::string_view> parts;
  size_t start = 0;
  for (;;) {
    size_t dot = name.find('.', start);
    if (dot == std::string_view::npos) {
      parts.push_back(name.substr(start));
      break;
    }
    parts.push_back(name.substr(start, dot - start));
    start = dot + 1;
  }
  return parts;
}

}  // namespace

VpiHandle VpiContext::HandleByName(const char* name, VpiHandle scope) {
  if (!name) return nullptr;

  // §38.21: a protected object cannot serve as the search scope. Unless
  // otherwise specified, asking for a handle relative to a protected scope is
  // an error; record it and return no handle.
  if (scope != nullptr && scope->is_protected) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_handle_by_name() with a protected scope is an error";
    return nullptr;
  }

  // §38.21: the name may be simple or hierarchical, so resolve it one path
  // component at a time from the leftmost (outermost) scope to the rightmost.
  std::vector<std::string_view> parts = VpiNamePathComponents(name);

  VpiHandle current = nullptr;
  for (size_t i = 0; i < parts.size(); ++i) {
    VpiHandle next = nullptr;
    if (current == nullptr && scope == nullptr) {
      // §38.21: with no scope the outermost component is searched for from the
      // top level of the design hierarchy.
      auto it = object_map_.find(parts[i]);
      next = (it == object_map_.end()) ? nullptr : it->second;
    } else {
      // §38.21: within a scope - the supplied scope for the first component, or
      // the previously resolved scope for a deeper one - the search is confined
      // to that scope's immediate contents and nothing outside it.
      VpiHandle within = (current == nullptr) ? scope : current;
      // §37.33 detail 9: vpi_handle_by_name() accepts a full name down to a
      // non-static data member even though such a member has no vpiFullName
      // property. The member lives on the class object the class variable
      // references, not on the variable itself, so descend into the referenced
      // object's members when stepping through a class variable.
      VpiHandle search = within;
      if (within->type == vpiClassVar && within->referenced_object) {
        search = within->referenced_object;
      }
      for (auto* child : search->children) {
        if (child->name == parts[i]) {
          next = child;
          break;
        }
      }
    }
    if (next == nullptr) return nullptr;

    // §38.21: a hierarchical name that passes through a protected scope is an
    // error - an intermediate component naming a protected object cannot be
    // descended into to reach a deeper object.
    bool is_last = (i + 1 == parts.size());
    if (!is_last && next->is_protected) {
      last_error_.state = kVpiError;
      last_error_.level = kVpiError;
      last_error_.message =
          "vpi_handle_by_name() through a protected scope is an error";
      return nullptr;
    }
    current = next;
  }

  if (current == nullptr) return nullptr;
  // §37.10 detail 6: imported items and compilation-unit objects must not be
  // reachable by name even when an object happens to be registered under it.
  if (!VpiHandleByNameAccessible(*current)) return nullptr;
  return current;
}

bool VpiHasAccessByIndex(int type) {
  switch (type) {
    case kVpiModule:         // §38.19: module indexes its ports
    case kVpiPort:           // a port indexes its bits
    case kVpiNet:            // a net indexes its bits
    case kVpiReg:            // a reg indexes its bits
    case vpiMemory:          // a memory indexes its words
    case vpiNetArray:        // an array net indexes its elements
    case vpiRegArray:        // a reg array indexes its elements
    case vpiPackedArrayVar:  // a packed array indexes its elements
    case vpiGenScopeArray:   // §37.85: a gen scope array indexes its gen scopes
      return true;
    default:
      return false;
  }
}

int VpiGenScopeArraySize(VpiHandle gen_scope_array) {
  // §37.85 detail 1: the size of a gen scope array is the number of elements in
  // the array, i.e. the gen scope objects it holds. It is counted from the
  // array's gen scope element children rather than read from any stored width.
  if (!gen_scope_array) return 0;
  int count = 0;
  for (auto* child : gen_scope_array->children) {
    if (child->type == vpiGenScope) ++count;
  }
  return count;
}

VpiHandle VpiContext::HandleByIndex(int index, VpiHandle parent) {
  if (!parent) return nullptr;

  // §38.19: unless otherwise specified, calling vpi_handle_by_index() for a
  // protected reference object is an error. Record it (§38.2) and hand back a
  // null handle.
  if (parent->is_protected) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_handle_by_index() on a protected object is an error";
    return nullptr;
  }

  // §38.19: the reference object must have the access-by-index property. An
  // object whose type offers no index-selected relationship cannot anchor an
  // index select, so there is no handle to return.
  if (!VpiHasAccessByIndex(parent->type)) return nullptr;

  // §38.19: return the sub-object selected by the index number. When no
  // sub-object carries the index, the selection is not a legal SystemVerilog
  // index select expression, so the result is a null handle.
  for (auto* child : parent->children) {
    if (child->index == index) return child;
  }
  return nullptr;
}

VpiHandle VpiContext::HandleByMultiIndex(int num_index, const int* index_array,
                                         VpiHandle parent) {
  if (!parent) return nullptr;

  // §38.20: as with vpi_handle_by_index(), calling vpi_handle_by_multi_index()
  // for a protected reference object is an error unless otherwise specified.
  // Record it (§38.2) and hand back a null handle.
  if (parent->is_protected) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_handle_by_multi_index() on a protected object is an error";
    return nullptr;
  }

  // §38.20: the reference object must carry the access-by-index property - the
  // same property vpi_handle_by_index() requires of its reference object.
  if (!VpiHasAccessByIndex(parent->type)) return nullptr;

  // §38.20: num_index gives how many indices index_array carries. With no
  // indices there is no index select expression to construct, so no subobject
  // is named.
  if (num_index <= 0 || index_array == nullptr) return nullptr;

  // §38.20: apply the indices in the order provided - leftmost first - following
  // the array dimension declaration from the leftmost to the rightmost range of
  // the reference handle, with an optional trailing bit-select index. Each step
  // descends to the subobject carrying that index. If any index names no
  // subobject the chain is not a legal SystemVerilog index select expression, so
  // the result is a null handle.
  VpiHandle current = parent;
  for (int i = 0; i < num_index; ++i) {
    VpiHandle next = nullptr;
    for (auto* child : current->children) {
      if (child->index == index_array[i]) {
        next = child;
        break;
      }
    }
    if (!next) return nullptr;
    current = next;
  }
  return current;
}

VpiHandle VpiContext::Handle(int type, VpiHandle ref) {
  // §37.43 detail 4: there is at most one active frame at a time in a given
  // thread, and an application reaches it with vpi_handle(vpiFrame, NULL).
  if (!ref && type == vpiFrame) return active_frame_;

  // §37.42 detail 3: the system task or function that invoked the application is
  // reached with vpi_handle(vpiSysTfCall, NULL).
  if (!ref && type == vpiSysTfCall) return current_systf_call_;

  // §37.82: vpi_handle(vpiActiveTimeFormat, NULL) reaches the system task call
  // that established the active time format - the $timeformat() call. Detail 1
  // requires NULL when $timeformat() has not been called; the recorded call is
  // null until then, so this branch returns NULL in that case.
  if (!ref && type == vpiActiveTimeFormat) return active_time_format_call_;

  if (!ref) return nullptr;

  // §38.18: unless otherwise specified, asking vpi_handle() for an object
  // related to a protected reference object is an error. Record it and hand
  // back a null handle.
  if (ref->is_protected) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message = "vpi_handle() on a protected object is an error";
    return nullptr;
  }

  // §37.3.5: it is an error to ask for a relation of an expression when the
  // implementation cannot reach the related handle without also evaluating an
  // expression that has side effects. The traversal is refused with an error and
  // a null handle rather than triggering the side effect.
  if (ref->property_needs_side_effect_eval) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_handle(): this relation cannot be determined without evaluating "
        "an expression with side effects";
    return nullptr;
  }

  // §37.84 details 1 and 2: vpi_handle(vpiUse, iterator) recovers the reference
  // handle the iterator was created over (detail 1). When that reference was null
  // - an iterator built over a null handle - the stored reference is null, so the
  // traversal hands back null in turn (detail 2). See also §38.23.
  if (type == vpiUse && ref->type == vpiIterator) return ref->iter_ref;

  // §37.11 detail 1: traversing vpiExpr from an instance array reaches the
  // operation object that lists the array's actual connections, not a child
  // whose own type happens to be vpiExpr.
  if (type == vpiExpr && VpiIsInstanceArrayType(ref->type)) {
    return VpiInstanceArrayConnections(ref);
  }

  // §37.13 detail 2: vpiExpr of an io decl reaches its designated connection -
  // a ref obj, virtual interface var, net, variable, or interface tf decl -
  // whose own type is not vpiExpr, so the shared traversal below cannot find it.
  if (type == vpiExpr && ref->type == vpiIODecl) {
    return VpiIoDeclExpr(ref);
  }

  // §37.29 detail 1: vpiExpr of a virtual interface var reaches the interface
  // instance assigned in its declaration (NULL when none was assigned). The
  // target's own type is an interface-expr kind, not vpiExpr, so the shared
  // traversal below cannot find it.
  if (type == vpiExpr && ref->type == vpiVirtualInterfaceVar) {
    return VpiVirtualInterfaceExpr(ref);
  }

  // §37.14 details 3, 4, and 10 (shared with §37.15): the higher and lower port
  // connections - also a ref obj's highConn/lowConn. These reach a designated
  // connection pointer, not a child found by type, and the helpers apply the
  // null-port / no-connection rules.
  if (type == vpiHighConn) return VpiHighConn(ref);
  if (type == vpiLowConn) return VpiLowConn(ref);

  // §37.33 detail 5: vpiClassObj of a class variable reaches the class object it
  // currently references. The object is shared - several variables may reference
  // it and one variable may reference different objects over its lifetime - so
  // it is reached through a designated reference, not a child found by type. A
  // class variable holding null references nothing, so the relation is NULL.
  if (type == vpiClassObj && ref->type == vpiClassVar) {
    return ref->referenced_object;
  }

  // §37.41 details 1-3: vpiReturn of a function reaches the variable that
  // captures its return value. Detail 1 makes a function contain that
  // return-capture object; detail 3 makes the relation always reach a var object,
  // even for a simple return; detail 2 makes it the implicit variable a caller
  // inspects to learn a user-defined return type. The target's own type is a
  // variable kind, not vpiReturn, so it is held as a designated pointer. Gated on
  // a function reference so the constant's other meanings (it shares a value with
  // vpiImmediateAssume) cannot reach this path. A task returns nothing, so it has
  // no return variable.
  if (type == vpiReturn && ref->type == vpiFunction) return ref->return_var;

  // §37.15 detail 3: vpiActual reaches the actual instantiated object a ref obj
  // is bound to (NULL when unbound).
  if (type == vpiActual && ref->type == vpiRefObj) return ref->actual;

  // §37.29 (Example 2): vpiActual of a virtual interface var reaches the
  // interface instance it currently holds - the actual passed to the new call
  // that bound it. It is NULL while the virtual interface is uninitialized.
  if (type == vpiActual && ref->type == vpiVirtualInterfaceVar) {
    return ref->actual;
  }

  // §37.48 detail 3: vpiActual of a clocking block reaches the concrete clocking
  // block selected through a virtual interface prefix, or NULL when that prefix
  // holds no value at the current simulation time.
  if (type == vpiActual && ref->type == vpiClockingBlock) {
    return VpiClockingBlockActual(ref);
  }

  // §37.48 detail 2: vpiPrefix of a clocking block reaches the virtual interface
  // var the clocking block expression is immediately prefixed by; NULL when the
  // clocking block is not a virtual-interface-prefixed expression.
  if (type == vpiPrefix && ref->type == vpiClockingBlock) {
    return VpiClockingBlockPrefix(ref);
  }

  // §37.48 detail 4: vpiExpr of a clocking io decl reaches the expression or ref
  // obj the io decl names.
  if (type == vpiExpr && ref->type == vpiClockingIODecl) {
    return VpiClockingIODeclExpr(ref);
  }

  // §37.15 detail 7: a ref obj's vpiTypespec is gated on the kind of its actual.
  if (type == vpiTypespec && ref->type == vpiRefObj) {
    return VpiRefObjTypespec(ref);
  }

  // §37.14 / §37.15 detail 4: vpiParent of a port bit reaches its port, and of a
  // ref obj reaches the ref obj it is a subelement of.
  if (type == vpiParent &&
      (ref->type == vpiRefObj || ref->type == vpiPortBit)) {
    return ref->parent;
  }

  // §37.30 detail 2: vpiParent of a modport interface typespec reaches the
  // interface typespec it belongs to; an interface interface typespec has none.
  if (type == vpiParent && ref->type == vpiInterfaceTypespec) {
    return VpiInterfaceTypespecParent(ref);
  }

  // §37.83: vpiParent of an attribute reaches the object the attribute is attached
  // to - the instance, net, statement, or other design object that owns it. That
  // owning object is held as the attribute's parent pointer.
  if (type == vpiParent && ref->type == vpiAttribute) {
    return ref->parent;
  }

  // §37.28 detail 2: vpiTypespec of a type parameter reaches the typespec it has
  // at the end of elaboration, returned without resolving typedef aliases. The
  // target is held as a designated pointer, so the generic walk cannot serve it.
  if (type == vpiTypespec && ref->type == vpiTypeParameter) {
    return VpiTypeParameterTypespec(ref);
  }

  // §37.28 detail 3: vpiExpr of a value or type parameter reaches its default -
  // the default value expression or default typespec - which is a designated
  // target whose own type is not vpiExpr, so the generic walk would miss it.
  if (type == vpiExpr &&
      (ref->type == vpiParameter || ref->type == vpiTypeParameter)) {
    return VpiParameterDefaultExpr(ref);
  }

  // §37.28 detail 4: vpiLhs of a param assign reaches the overridden value or
  // type parameter, a parameter-kind child rather than one whose own type is
  // vpiLhs.
  if (type == vpiLhs && ref->type == vpiParamAssign) {
    return VpiParamAssignLhs(ref);
  }

  // §37.28 detail 5: vpiLeftRange / vpiRightRange of a value parameter reach the
  // bounds of its explicit range, or NULL when it was declared without one.
  if (type == vpiLeftRange && ref->type == vpiParameter) {
    return VpiParameterLeftRange(ref);
  }
  if (type == vpiRightRange && ref->type == vpiParameter) {
    return VpiParameterRightRange(ref);
  }

  // §37.65 detail 1: vpiStmt of an event control reaches the statement it guards,
  // except that an event control associated with an assignment always reports a
  // null statement rather than the first statement child the generic traversal
  // below would otherwise find.
  if (type == vpiStmt && ref->type == vpiEventControl) {
    return VpiEventControlStmt(ref);
  }

  // §37.68 detail 1: vpiStmt of a delay control reaches the statement it guards,
  // except that a delay control associated with an assignment always reports a
  // null statement rather than the first statement child the generic traversal
  // below would otherwise find.
  if (type == vpiStmt && ref->type == vpiDelayControl) {
    return VpiDelayControlStmt(ref);
  }

  // §37.66: vpiCondition of a while or repeat statement reaches its controlling
  // condition expression. The condition's own type is an expression kind, not the
  // vpiCondition relation tag, so the generic traversal below cannot find it. The
  // relation is gated on the loop statement kinds so it does not also serve the
  // vpiCondition edge other diagrams draw (for instance the waits of §37.67). The
  // loop body, drawn by the diagram's unlabeled edge to a statement, is reached by
  // the generic vpiStmt traversal below and needs no special case here.
  if (type == vpiCondition && VpiIsWhileOrRepeatType(ref->type)) {
    return VpiLoopConditionExpr(ref);
  }

  // §37.71: vpiCondition of an if or if-else statement reaches its controlling
  // condition expression. As with the loop statements above, the condition's own
  // type is an expression kind rather than the vpiCondition relation tag, so the
  // generic traversal below cannot find it. The relation is gated on the
  // conditional statement kinds so it does not also serve the vpiCondition edge
  // other diagrams draw. The then-branch body, drawn by the diagram's unlabeled
  // edge to a statement, is reached by the generic vpiStmt traversal below.
  if (type == vpiCondition && VpiIsIfOrIfElseType(ref->type)) {
    return VpiIfConditionExpr(ref);
  }

  // §37.74: vpiCondition of a for statement reaches its controlling condition
  // expression. As with the loop and conditional statements above, the
  // condition's own type is an expression kind rather than the vpiCondition
  // relation tag, so the generic traversal below cannot find it. The relation is
  // gated on the for statement kind so it does not also serve the vpiCondition
  // edge other diagrams draw. The for statement's initialization and increment
  // statements (vpiForInitStmt/vpiForIncStmt) and its body (the diagram's
  // unlabeled edge to a statement) are reached by the generic traversal and
  // iteration and need no special case here.
  if (type == vpiCondition && ref->type == vpiFor) {
    return VpiForConditionExpr(ref);
  }

  // §37.75: vpiCondition of a do-while statement reaches its controlling
  // condition expression. As with the loop and conditional statements above, the
  // condition's own type is an expression kind rather than the vpiCondition
  // relation tag, so the generic traversal below cannot find it. The relation is
  // gated on the do-while kind so it does not also serve the vpiCondition edge
  // other diagrams draw. The do-while's body (the diagram's unlabeled edge to a
  // statement) is reached by the generic vpiStmt traversal below and needs no
  // special case here.
  if (type == vpiCondition && ref->type == vpiDoWhile) {
    return VpiDoWhileConditionExpr(ref);
  }

  // §37.78: vpiCondition of a return statement reaches the value it returns - the
  // single edge the return statement diagram draws. As with the loop and
  // conditional statements above, the value's own type is an expression kind
  // rather than the vpiCondition relation tag, so the generic traversal below
  // cannot find it. The relation is gated on the return statement kind so it does
  // not also serve the vpiCondition edge other diagrams draw. A return that yields
  // no value (a void function or task return) has no expression child and falls
  // through to report null.
  if (type == vpiCondition && ref->type == vpiReturnStmt) {
    return VpiReturnConditionExpr(ref);
  }

  // §37.79: the procedural continuous assignment family - an assign statement, a
  // force, a deassign, and a release - reaches its target through vpiLhs, and the
  // two that supply a value (the assign statement and the force) reach that value
  // through vpiRhs. Each side is an expression whose own type is an expression
  // kind, not the vpiLhs / vpiRhs relation tag, so the generic walk below cannot
  // find it; both are held as designated pointers. The vpiLhs relation is scoped
  // to these four kinds so it does not disturb the vpiLhs edge other diagrams draw
  // (for instance the parameter assignment of §37.28, handled above). A deassign
  // or release draws no vpiRhs edge: it falls through the rhs gate below and the
  // generic walk reports null, since it names a target but supplies no value.
  if (type == vpiLhs &&
      (ref->type == vpiAssignStmt || ref->type == vpiForce ||
       ref->type == vpiDeassign || ref->type == vpiRelease)) {
    return ref->lhs;
  }
  if (type == vpiRhs && (ref->type == vpiAssignStmt || ref->type == vpiForce)) {
    return ref->rhs;
  }

  // §37.76: an alias statement reaches the two sides of the alias it establishes -
  // its left-hand side expression through vpiLhs and its right-hand side
  // expression through vpiRhs. As with the procedural continuous assignment family
  // of §37.79 above, each side is an expression whose own type is an expression
  // kind rather than the vpiLhs / vpiRhs relation tag, so the generic walk below
  // cannot find it; both are held as the designated lhs / rhs pointers. The
  // relations are gated on the alias statement kind so they do not disturb the
  // vpiLhs / vpiRhs edges other diagrams draw. The diagram's remaining edge, the
  // bidirectional structural link between the alias statement and the enclosing
  // instance, is reached by the generic traversal and needs no special case here.
  if (type == vpiLhs && ref->type == vpiAliasStmt) {
    return ref->lhs;
  }
  if (type == vpiRhs && ref->type == vpiAliasStmt) {
    return ref->rhs;
  }

  // §37.71: vpiElseStmt of an if-else statement reaches its else-branch body.
  // The relation is drawn only from the if-else grouping, never from a plain if,
  // so it is gated on the if-else kind. The else statement's own type is a
  // statement kind rather than the vpiElseStmt relation tag, so the generic
  // traversal below cannot find it.
  if (type == vpiElseStmt && ref->type == vpiIfElse) {
    return VpiIfElseStmt(ref);
  }

  // §37.69: vpiExpr of a repeat control reaches its count expression - the
  // repetition number of an intra-assignment repeat event control. The count's
  // own type is an expression kind, not the vpiExpr relation tag, so the generic
  // traversal below cannot find it. The relation is gated on the repeat control
  // kind so it does not disturb the vpiExpr edges other diagrams draw (for
  // instance a parameter's default, §37.28). The diagram's other edge, to the
  // event control, is reached by the generic traversal below because that child's
  // own type is vpiEventControl and so needs no special case here.
  if (type == vpiExpr && ref->type == vpiRepeatControl) {
    return VpiRepeatControlExpr(ref);
  }

  // §37.77: vpiExpr of a disable statement reaches the named scope it disables -
  // a task, function, named begin, or named fork. That scope's own type is one of
  // those scope kinds, not the vpiExpr relation tag, so the generic traversal
  // below cannot find it. The relation is gated on the plain disable statement so
  // a disable fork (vpiDisableFork), which disables the active process's children
  // and names no scope, draws no such edge and falls through to report null.
  if (type == vpiExpr && ref->type == vpiDisable) {
    return VpiDisableExpr(ref);
  }

  // §37.12 detail 5: vpiStmt of a task or function reaches its body - null when
  // the task/func has no statements, the lone statement when it has one, and the
  // unnamed begin grouping them when it has more than one. The body's own type
  // is a statement kind (a begin or an atomic statement), not vpiStmt, so the
  // generic traversal below cannot find it.
  if (type == vpiStmt && VpiIsTaskFuncType(ref->type)) {
    return VpiTaskFuncStmt(ref);
  }

  // §37.12 details 2 and 3: the scope of a loop control variable is the loop
  // statement that declares it - a foreach statement always (detail 3), or a for
  // statement when that for statement is itself a scope, i.e. it declares its
  // loop variables locally (detail 2, vpiLocalVarDecls). The variable is a child
  // of the loop, so its enclosing scope is the loop object rather than something
  // the generic walk below would find. A for statement that is not a scope leaves
  // the query to the generic handling.
  if (type == vpiScope && ref->parent && VpiIsLoopControlVarType(ref->type)) {
    if (ref->parent->type == vpiForeachStmt) return ref->parent;
    if (ref->parent->type == vpiFor && ref->parent->local_var_decls) {
      return ref->parent;
    }
  }

  // §37.35 detail 4: vpiIndex from a primitive reaches the index expression that
  // locates the primitive within its primitive array. The transition is only
  // meaningful for an array-member primitive; a primitive that is not part of a
  // primitive array reports NULL here rather than letting the generic walk find
  // some other expr child.
  if (type == vpiIndex && VpiObjectIsPrimitive(ref->type)) {
    return ref->array_member ? ref->index_expr : nullptr;
  }

  // §37.9 detail 1: vpiIndex from a program reaches the index expression that
  // locates the program within its instance array. As with an array-member
  // primitive, a program that is not an element of an instance array reports
  // NULL here rather than letting the generic walk find some other expr child.
  if (type == vpiIndex && ref->type == vpiProgram) {
    return ref->array_member ? ref->index_expr : nullptr;
  }

  // §37.6 detail 1: vpiIndex from an interface reaches the index expression that
  // locates the interface within its instance array. As with an array-member
  // program or primitive, an interface that is not an element of an instance
  // array reports NULL here rather than letting the generic walk find some other
  // expr child.
  if (type == vpiIndex && ref->type == vpiInterface) {
    return ref->array_member ? ref->index_expr : nullptr;
  }

  // §37.5 detail 2: vpiIndex from a module reaches the index expression that
  // locates the module within its module array. As with an array-member
  // program, primitive, or interface, a module that is not an element of a
  // module array reports NULL here rather than letting the generic walk find
  // some other expr child.
  if (type == vpiIndex && ref->type == kVpiModule) {
    return ref->array_member ? ref->index_expr : nullptr;
  }

  // §37.85 (figure): vpiIndex from a gen scope reaches the index expression that
  // locates the gen scope within its gen scope array. As with an array-member
  // module, program, interface, or primitive, a gen scope that is not an element
  // of a gen scope array reports NULL here rather than letting the generic walk
  // find some other expr child.
  if (type == vpiIndex && ref->type == vpiGenScope) {
    return ref->array_member ? ref->index_expr : nullptr;
  }

  // §37.42 detail 2: vpiPrefix of a method call reaches the object the method is
  // applied to (the class var "packet" in "packet.send()"). The prefix is held as
  // a designated pointer (it is an expr, not a vpiPrefix-typed child); a tf call
  // that is not a method call carries no prefix.
  if (type == vpiPrefix && VpiIsMethodCallType(ref->type)) {
    return ref->tf_prefix;
  }

  // §37.61 detail 1: vpiPrefix of a dynamically prefixed object - a simple
  // expression, part-select, indexed part-select, named event, or named event
  // array - reaches the class var, virtual interface var, or clocking block that
  // prefixes it in the source. The prefix is held as a designated pointer (its
  // own type is none of these relation tags), so the generic walk below cannot
  // serve it; an object that is not prefixed reports NULL. The relation is non-
  // NULL exactly when the object represents an expression prefixed by a virtual
  // interface or clocking block, or is all or part of a non-static class
  // property prefixed by a class var.
  if (type == vpiPrefix && VpiIsDynamicPrefixSourceType(ref->type)) {
    return ref->prefix;
  }

  // §37.42 detail 1: vpiWith of a method call reaches its with-clause (an
  // expression, or a constraint), but the relation is available only for the
  // methods that take a with clause - randomize and array-locator methods. For
  // any other method call it reports NULL even when a with object is attached.
  if (type == vpiWith && VpiIsMethodCallType(ref->type)) {
    return ref->tf_with_method ? ref->tf_with : nullptr;
  }

  // §37.42 detail 11: a built-in method func call has no user function object, so
  // vpiFunction reports NULL; a built-in method task call likewise reports NULL
  // for vpiTask. A user-defined (non-built-in) method call falls through to the
  // generic traversal below, which finds its function/task child.
  if (type == vpiFunction && ref->type == vpiMethodFuncCall &&
      ref->builtin_method) {
    return nullptr;
  }
  if (type == vpiTask && ref->type == vpiMethodTaskCall &&
      ref->builtin_method) {
    return nullptr;
  }

  // §37.40 detail 1: a timing check's vpiTchkRefTerm relation denotes its
  // reference event (or controlled reference event), and vpiTchkDataTerm denotes
  // its data event when the check has one. Both reach tchk term objects, whose
  // own type (vpiTchkTerm) differs from the relation enum, so the generic walk
  // below cannot find them; they are held as designated pointers. A check with
  // no data event reports NULL for vpiTchkDataTerm ("if any").
  if (type == vpiTchkRefTerm && ref->type == vpiTchk) return ref->tchk_ref_term;
  if (type == vpiTchkDataTerm && ref->type == vpiTchk) {
    return ref->tchk_data_term;
  }

  // §37.45: a delay device reaches its input delay term through vpiInTerm and its
  // output delay term through vpiOutTerm. Both terms are delay term objects whose
  // own type (vpiDelayTerm) differs from the relation enum, so the generic walk
  // below cannot find them; they are held as designated pointers. The relations
  // are specific to a delay device, so they do not reach a stray delay term on
  // any other object.
  if (type == vpiInTerm && ref->type == vpiDelayDevice) return ref->in_term;
  if (type == vpiOutTerm && ref->type == vpiDelayDevice) return ref->out_term;

  // §37.38 detail 1: a foreach constraint's vpiVariables relation reaches the
  // variable that represents the array being indexed. The array variable's own
  // type is a variable kind, not the relation enum, so the generic walk below
  // cannot find it; it is held as a designated pointer. The relation is specific
  // to a foreach constraint, so it does not pick up a stray variable on any other
  // object.
  if (type == vpiVariables && ref->type == vpiConstrForEach) {
    return ref->foreach_array;
  }

  // §37.75 detail 1: a foreach statement's vpiVariables relation reaches the
  // variable being indexed - the packed array, unpacked array, or string var the
  // loop iterates over. As with the foreach constraint above, that variable's own
  // type is a variable kind rather than the relation enum, so it is held as a
  // designated pointer rather than found by the generic walk. The relation is
  // specific to a foreach statement, so it does not pick up a stray variable on
  // any other object.
  if (type == vpiVariables && ref->type == vpiForeachStmt) {
    return ref->foreach_array;
  }

  // §37.39 detail 1: vpiModule from a specify-block path (mod path) is kept for
  // backward compatibility, but it shall report NULL when that specify block
  // lives in an interface rather than a module. Walk outward to the innermost
  // enclosing instance: reaching an interface first means there is no owning
  // module to return, even when the interface is itself instantiated inside a
  // module; reaching a module first reports that module. New code is meant to
  // use the vpiInstance relation, which reaches either container.
  if (type == kVpiModule && ref->type == vpiModPath) {
    for (VpiObject* scope = ref->parent; scope; scope = scope->parent) {
      if (scope->type == vpiInterface) return nullptr;
      if (scope->type == kVpiModule) return scope;
    }
    return nullptr;
  }

  // §37.23 detail 2: a nettype declaration that is an alias of another nettype
  // declaration reaches the aliased nettype through vpiNetTypedefAlias, which
  // reports a non-null handle to that nettype. The aliased nettype's own type is
  // vpiNetTypedef, not the relation tag, so it is kept as a designated pointer
  // rather than found by the generic walk. A nettype that is not an alias has no
  // such target and reports NULL.
  if (type == vpiNetTypedefAlias && ref->type == vpiNetTypedef) {
    return ref->nettype_alias;
  }

  // §37.23 detail 1: a nettype declaration reaches its associated resolution
  // function through vpiWith. A nettype declared without a resolution function
  // reports NULL. (vpiWith on a method call is served by the §37.42 branch
  // above; here the relation originates from a nettype declaration, a distinct
  // object kind, so the two never collide.)
  if (type == vpiWith && ref->type == vpiNetTypedef) {
    return ref->nettype_with;
  }

  if (ref->parent && ref->parent->type == type) return ref->parent;

  for (auto* child : ref->children) {
    if (child->type == type) return child;
  }
  return nullptr;
}

// ===========================================================================
// §37.21 Variable drivers and loads.
// ===========================================================================

bool VpiIsVariableDriverType(int type) {
  // §37.21 (figure, variable drivers): the kinds that drive a variable - a port,
  // a force, a continuous assignment, a single bit of a continuous assignment, or
  // a procedural assignment statement.
  switch (type) {
    case vpiPort:
    case vpiForce:
    case vpiContAssign:
    case vpiContAssignBit:
    case vpiAssignStmt:
      return true;
    default:
      return false;
  }
}

bool VpiIsVariableLoadType(int type) {
  // §37.21 (figure, variable loads): the kinds that read a variable. The figure
  // lists the driver kinds without a port - an assignment statement, a force, and
  // a continuous assignment or single bit of one - because a port only ever
  // drives a variable, it never loads it.
  switch (type) {
    case vpiForce:
    case vpiContAssign:
    case vpiContAssignBit:
    case vpiAssignStmt:
      return true;
    default:
      return false;
  }
}

// ===========================================================================
// §37.46 Net drivers and loads.
// ===========================================================================

bool VpiIsNetDriverType(int type) {
  // §37.46 (figure, net drivers): a port, a force, a delay terminal, a
  // continuous assignment (whole or single bit), or a primitive terminal. Unlike
  // a variable (§37.21) a net is not driven by a procedural assignment statement.
  switch (type) {
    case vpiPort:
    case vpiForce:
    case vpiDelayTerm:
    case vpiContAssign:
    case vpiContAssignBit:
    case vpiPrimTerm:
      return true;
    default:
      return false;
  }
}

bool VpiIsNetLoadType(int type) {
  // §37.46 (figure, net loads): a delay terminal, an assignment statement, a
  // force, a continuous assignment (whole or single bit), or a primitive
  // terminal. A port is excluded here; detail 1 governs when a port is a load.
  switch (type) {
    case vpiDelayTerm:
    case vpiAssignStmt:
    case vpiForce:
    case vpiContAssign:
    case vpiContAssignBit:
    case vpiPrimTerm:
      return true;
    default:
      return false;
  }
}

namespace {

// §37.46 detail 1: a concatenation operation. The operand connections it groups
// drive/load their nets individually, so a concatenation on a port does not make
// the whole port a complex-expression load.
bool VpiIsConcatenationExpression(VpiObject* expr) {
  return expr->type == vpiOperation &&
         (expr->op_type == vpiConcatOp || expr->op_type == vpiMultiConcatOp);
}

}  // namespace

bool VpiPortIsComplexExpressionLoad(VpiHandle port) {
  // §37.46 detail 1: a complex expression on an input port - an operation other
  // than a concatenation - loads the nets it reads, and the port is then the load
  // object reported when iterating the net's loads. A simple reference is a
  // direct connection rather than a complex-expression load, a concatenation's
  // operands connect their nets individually, and only an input port loads this
  // way. The complex expression itself is reached through vpiHighConn (§37.14).
  if (!port || port->type != vpiPort) return false;
  if (port->direction != vpiInput) return false;
  VpiObject* expr = port->high_conn;
  if (!expr || expr->type != vpiOperation) return false;
  return !VpiIsConcatenationExpression(expr);
}

namespace {

// §37.21 detail 1: a structure, union, or class variable owns the additional
// driver/load collection behaviour - the relation must also reach drivers/loads
// of bit/part-selects and nested members of the variable.
bool VpiIsStructUnionOrClassVar(int type) {
  return type == vpiStructVar || type == vpiUnionVar || type == vpiClassVar;
}

// §37.21 detail 1: the select kinds whose drivers/loads count toward an
// aggregate variable - a bit-select or either form of part-select.
bool VpiIsVariableSelectType(int type) {
  return type == vpiBitSelect || type == vpiPartSelect ||
         type == vpiIndexedPartSelect;
}

// §37.21 detail 1: the children worth descending into when gathering the drivers
// or loads of an aggregate variable - a bit-select or part-select of the
// variable, or a member nested inside it (itself any variable kind, including a
// further aggregate that is walked recursively).
bool VpiIsVariableSelectOrMemberType(int type) {
  if (VpiIsVariableSelectType(type)) return true;
  if (VpiIsLogicVarType(type) || VpiIsArrayVarType(type)) return true;
  switch (type) {
    case vpiStructVar:
    case vpiUnionVar:
    case vpiClassVar:
    case vpiEnumVar:
    case vpiPackedArrayVar:
    case vpiVariables:
      return true;
    default:
      return false;
  }
}

// §37.21 (figure) + detail 1: gather a variable's drivers (want_driver) or loads
// into the iterator. The variable's own driver/load children are always
// collected. When descend is set - the variable is a structure, union, or class
// variable - the walk also recurses through the variable's bit/part-selects and
// nested members so their drivers/loads are included as well.
void CollectVariableDriversOrLoads(VpiObject* node, bool want_driver,
                                   bool descend, VpiObject* iter) {
  for (auto* child : node->children) {
    bool is_target = want_driver ? VpiIsVariableDriverType(child->type)
                                 : VpiIsVariableLoadType(child->type);
    if (is_target) {
      iter->children.push_back(child);
    } else if (descend && VpiIsVariableSelectOrMemberType(child->type)) {
      CollectVariableDriversOrLoads(child, want_driver, descend, iter);
    }
  }
}

// §37.46 (figure) + detail 1: gather a net's drivers (want_driver) or loads into
// the iterator. A driver/load is one of the object-kind children the figure
// lists. On the driver side a port is always a driver; on the load side a port is
// reported only when it carries a complex, non-concatenation expression on an
// input (detail 1).
void CollectNetDriversOrLoads(VpiObject* node, bool want_driver,
                              VpiObject* iter) {
  for (auto* child : node->children) {
    if (want_driver) {
      if (VpiIsNetDriverType(child->type)) iter->children.push_back(child);
    } else if (child->type == vpiPort) {
      if (VpiPortIsComplexExpressionLoad(child)) iter->children.push_back(child);
    } else if (VpiIsNetLoadType(child->type)) {
      iter->children.push_back(child);
    }
  }
}

}  // namespace

VpiHandle VpiContext::Iterate(int type, VpiHandle ref) {
  // §37.42: a tf call's arguments are reached through vpiArgument. The arguments
  // are the call's argument-kind children (an expr, interface expr, scope,
  // primitive, or named event(-array)), not children whose own type is
  // vpiArgument, so this iteration is recognized specially below.
  bool tf_argument_iteration =
      ref && VpiIsTfCallType(ref->type) && type == vpiArgument;

  // §37.27 detail 1: vpiWaitingProcesses on a named event reaches the threads of
  // every process - static or dynamic - currently waiting on that event. The
  // relation is named for the processes but the objects it reaches are threads,
  // so it is recognized specially rather than matched against the relation name.
  bool named_event_waiting_iteration =
      ref && ref->type == vpiNamedEvent && type == vpiWaitingProcesses;

  // §37.27 detail 2: vpiIndex on a named event reaches the index expressions that
  // locate it within an array, starting with the index for the named event and
  // working outward. A named event that is not an array element has no such
  // indices, so the iteration finds none and reports NULL. The relation reaches
  // exprs, not children whose own type is vpiIndex, so it too is special.
  bool named_event_index_iteration =
      ref && ref->type == vpiNamedEvent && type == vpiIndex;

  // §37.18 detail 3: vpiElement on a packed array variable reaches its
  // subelements - struct var, union var, enum var, or (for a multidimensioned
  // packed array) another packed array var - one dimension level at a time. The
  // relation reaches those variable kinds, not children whose own type is
  // literally vpiElement, so it is recognized specially below.
  bool packed_array_var_element_iteration =
      ref && ref->type == vpiPackedArrayVar && type == vpiElement;

  // §37.18 detail 6: vpiIndex on a packed array variable reaches the index
  // expressions that locate a subelement within its vpiParent, beginning with
  // the subelement's own index and working outward (the right-to-left textual
  // order). Like the named-event case it reaches exprs, not children whose own
  // type is vpiIndex.
  bool packed_array_var_index_iteration =
      ref && ref->type == vpiPackedArrayVar && type == vpiIndex;

  // §37.24 detail 2: vpiElement on an interconnect array reaches its subelements
  // one dimension level at a time - each is itself an interconnect array (a
  // further dimension) or a leaf interconnect net - rather than children whose
  // own type is literally vpiElement.
  bool interconnect_array_element_iteration =
      ref && ref->type == vpiInterconnectArray && type == vpiElement;

  // §37.24 detail 1: vpiElement on an interconnect net reaches the net's array
  // elements, but only when the typespec it connects to has a packed or unpacked
  // array data type; a net connected to a non-array type has no such elements.
  bool interconnect_net_element_iteration =
      ref && ref->type == vpiInterconnectNet && type == vpiElement &&
      VpiIsInterconnectArrayDataTypespec(VpiInterconnectNetTypespecType(ref));

  // §37.24 detail 1: vpiMember on an interconnect net reaches the net's struct
  // members, but only when the typespec it connects to has a packed or unpacked
  // struct (or union) data type.
  bool interconnect_net_member_iteration =
      ref && ref->type == vpiInterconnectNet && type == vpiMember &&
      VpiIsInterconnectStructDataTypespec(VpiInterconnectNetTypespecType(ref));

  // §37.20 detail 1: vpiMemoryWord is a backwards-compatibility relation. A
  // memory has been generalized to a reg array (vpiRegArray) and its words to
  // reg objects (vpiReg). Iterating vpiMemoryWord over a reg array therefore
  // reaches its reg word objects - children whose own kind is vpiReg, not
  // children typed literally vpiMemoryWord - so the relation is recognized
  // specially. The variable and variable-array definitions these objects reuse
  // belong to §37.17.
  bool memory_word_iteration =
      ref && VpiIsArrayVarType(ref->type) && type == vpiMemoryWord;

  // §37.46 (figure): vpiDriver on a net reaches the net's driver objects - a
  // port, a force, a delay terminal, a continuous assignment (whole or single
  // bit), or a primitive terminal - and vpiLoad reaches its load objects. The
  // net case differs from the variable case below: an assignment statement loads
  // but does not drive a net, and a port loads a net only through the
  // complex-expression rule (detail 1), so the net relations are collected by
  // net-specific machinery rather than reused from §37.21.
  bool net_driver_iteration =
      ref && (ref->type == vpiNet || ref->type == vpiNetBit) &&
      type == vpiDriver;
  bool net_load_iteration =
      ref && (ref->type == vpiNet || ref->type == vpiNetBit) &&
      type == vpiLoad;

  // §37.21 (figure): vpiDriver on a variable reaches the variable's driver
  // objects - a port, a force, a continuous assignment (whole or single bit), or
  // a procedural assignment statement - rather than children whose own type is
  // literally vpiDriver. Likewise vpiLoad reaches the variable's load objects. A
  // net reference is handled by §37.46 above, not here.
  bool variable_driver_iteration =
      ref && type == vpiDriver && !net_driver_iteration;
  bool variable_load_iteration =
      ref && type == vpiLoad && !net_load_iteration;

  // §37.5 detail 1: the top-level modules are accessed by iterating vpiModule
  // with a NULL reference object. Only top-level modules answer that iteration;
  // a module nested inside another scope is also a vpiModule object but is
  // reached through its parent's internal scope, so it is excluded here.
  bool top_module_iteration = !ref && type == kVpiModule;

  // §37.31 detail 1 and §37.33 detail 6: vpiMethods on a class defn or a class
  // object reaches its methods, which are task and function objects (the "task
  // func" node) rather than children whose own type is literally vpiMethods, so
  // this iteration is matched specially and filtered to drop implicit built-in
  // methods (those carrying no explicit declaration) below.
  bool class_methods_iteration =
      ref && (ref->type == vpiClassDefn || ref->type == vpiClassObj) &&
      type == vpiMethods;

  // §37.33 detail 3: vpiWaitingProcesses on a class object - a mailbox or a
  // semaphore - reaches the threads of the processes waiting on it, like the
  // named-event case (§37.27). The relation reaches thread objects, not children
  // whose own type is literally vpiWaitingProcesses, so it is matched specially.
  bool class_obj_waiting_iteration =
      ref && ref->type == vpiClassObj && type == vpiWaitingProcesses;

  // §37.33 detail 4: vpiMessages on a class object - a mailbox - reaches the
  // messages it holds, which are expression objects rather than children whose
  // own type is literally vpiMessages, so it too is matched specially.
  bool class_obj_messages_iteration =
      ref && ref->type == vpiClassObj && type == vpiMessages;

  // §37.31 detail 3: vpiConstraint on a class defn reaches the class's constraint
  // children directly (a generic type match), but the iteration must return only
  // normal constraints, so inline constraints are dropped below.
  bool class_constraint_iteration =
      ref && ref->type == vpiClassDefn && type == vpiConstraint;

  // §37.31 detail 5: vpiDerivedClasses on a class defn reaches the class defns
  // derived from it - again class-defn objects, not children whose own type is
  // vpiDerivedClasses - so the relation is recognized specially.
  bool class_derived_iteration =
      ref && ref->type == vpiClassDefn && type == vpiDerivedClasses;

  // §37.31 detail 6: the vpiArgument iteration from an extends object yields the
  // expressions used for constructor chaining (8.17). The arguments are
  // expression children, not children whose own type is vpiArgument, so this is
  // matched specially like a tf call's argument iteration.
  bool extends_argument_iteration =
      ref && ref->type == vpiExtends && type == vpiArgument;

  // §37.12 detail 7: a scope's vpiVirtualInterfaceVar iteration reaches the
  // virtual interface vars it declares (§37.29). When the scope declares an array
  // of virtual interfaces, the iteration yields each element of the array
  // separately, so the array var child is expanded rather than returned whole.
  bool vif_iteration = ref && type == vpiVirtualInterfaceVar;

  // §37.12 detail 7: a scope's vpiVariables iteration reports an array of virtual
  // interfaces as the single array var that declares it (not its elements),
  // alongside the scope's ordinary variables.
  bool variables_iteration = ref && type == vpiVariables;

  // §37.12 detail 4: a scope's vpiImport iteration reaches the objects actually
  // imported into it through import declarations - the items genuinely referenced
  // across the import (marked imported), rather than children whose own type is
  // literally vpiImport or items merely made visible by the import.
  bool import_iteration = ref && type == vpiImport;

  // §37.40 detail 2: a timing check's vpiExpr iteration reaches its arguments.
  // The reference, controlled-reference, and data events are returned as tchk
  // term objects (vpiTchkTerm); every other argument keeps the type of its
  // expression. The relation therefore reaches those terms and expressions, not
  // children whose own type is literally vpiExpr, so it is matched specially.
  bool tchk_expr_iteration = ref && ref->type == vpiTchk && type == vpiExpr;

  // §37.38 detail 2: vpiLoopVars on a foreach constraint walks the constraint's
  // index variables in left-to-right order. The objects reached are the index
  // variables (and null-op placeholders for skipped positions), not children
  // whose own type is literally vpiLoopVars, so the iteration is built from the
  // constraint's dedicated loop-var list rather than matched by type.
  bool constr_foreach_loopvars_iteration =
      ref && ref->type == vpiConstrForEach && type == vpiLoopVars;

  // §37.75 detail 2: vpiLoopVars on a foreach statement walks the loop's index
  // variables in left-to-right order. As with the foreach constraint above, the
  // objects reached are the index variables (and null-op placeholders for skipped
  // positions), not children whose own type is literally vpiLoopVars, so the
  // iteration is built from the statement's dedicated loop-var list rather than
  // matched by type.
  bool foreach_stmt_loopvars_iteration =
      ref && ref->type == vpiForeachStmt && type == vpiLoopVars;

  // §37.38 detail 3: vpiConstraintExpr on a constraint-expression container - an
  // implication, constraint if, constraint if-else, or foreach constraint -
  // walks the body expressions it holds in source order. They are reached from a
  // dedicated body list, not matched as children whose own type is
  // vpiConstraintExpr, so this iteration is recognized specially.
  bool constraint_expr_iteration =
      ref && type == vpiConstraintExpr &&
      VpiIsConstraintExprContainerType(ref->type);

  // §38.23: unless otherwise specified, iterating the relationships of a
  // protected object is an error, so no iterator is produced. §37.42 detail 10
  // carves out one exception: a protected system task or function call shall
  // still allow iteration over its vpiArgument relation. Every other protected
  // iteration is still refused.
  if (ref && ref->is_protected && !tf_argument_iteration) return nullptr;

  // §37.72 detail 2: a default case item has no condition expression, so
  // iterating its match expressions (vpi_iterate(vpiExpr, item)) returns NULL.
  // This holds even when the object carries other children, distinguishing the
  // default item from a non-default item that simply has no conditions yet.
  if (ref && ref->type == vpiCaseItem && type == vpiExpr &&
      ref->default_case_item) {
    return nullptr;
  }

  // §38.23: the handle returned is an iterator whose own type is vpiIterator;
  // the requested object type only selects which related objects it walks. The
  // reference object is remembered so it can be recovered through vpiUse.
  auto* iter = new VpiObject();
  iter->type = vpiIterator;
  iter->iter_ref = ref;
  // §37.84: remember the object kind being walked so the iterator can report it
  // through vpi_get(vpiIteratorType, iterator).
  iter->iter_type = type;
  iter->scan_index = 0;

  // §37.49: vpiAssertion names the assertion class rather than a single object
  // kind, so iterating it collects every object the class groups (the circle
  // relation, when ref is null) instead of matching one exact type.
  auto matches = [type, ref, tf_argument_iteration,
                  named_event_waiting_iteration, named_event_index_iteration,
                  packed_array_var_element_iteration,
                  packed_array_var_index_iteration, class_methods_iteration,
                  class_obj_waiting_iteration, class_obj_messages_iteration,
                  class_derived_iteration, memory_word_iteration,
                  extends_argument_iteration, interconnect_array_element_iteration,
                  interconnect_net_element_iteration,
                  interconnect_net_member_iteration,
                  tchk_expr_iteration](int obj_type) {
    // §37.20 detail 1: a reg array's vpiMemoryWord iteration collects its reg
    // word objects (vpiReg), the backwards-compatible form of the legacy memory
    // words, rather than children whose own type is literally vpiMemoryWord.
    if (memory_word_iteration) return obj_type == kVpiReg;
    if (type == vpiAssertion) return VpiIsAssertionType(obj_type);
    // §37.31 detail 1 / §37.33 detail 6: a class defn's or class object's
    // vpiMethods iteration collects its method objects - the tasks and functions
    // declared as class items - rather than children whose own type is literally
    // vpiMethods.
    if (class_methods_iteration) return VpiIsClassMethodType(obj_type);
    // §37.31 detail 5: a class defn's vpiDerivedClasses iteration collects the
    // class defns derived from it.
    if (class_derived_iteration) return obj_type == vpiClassDefn;
    // §37.31 detail 6: an extends object's vpiArgument iteration collects the
    // expressions supplied for constructor chaining.
    if (extends_argument_iteration) return VpiIsExprType(obj_type);
    // §37.27 detail 1: a named event's vpiWaitingProcesses iteration collects the
    // thread objects of the waiting processes, not children typed
    // vpiWaitingProcesses.
    if (named_event_waiting_iteration) return obj_type == vpiThread;
    // §37.33 detail 3: a class object's vpiWaitingProcesses iteration likewise
    // collects the thread objects of the processes waiting on it.
    if (class_obj_waiting_iteration) return obj_type == vpiThread;
    // §37.33 detail 4: a class object's vpiMessages iteration collects the
    // message objects it holds - expressions - not children typed vpiMessages.
    if (class_obj_messages_iteration) return VpiIsExprType(obj_type);
    // §37.27 detail 2: a named event's vpiIndex iteration collects the index
    // expressions locating it within its array.
    if (named_event_index_iteration) return VpiIsExprType(obj_type);
    // §37.18 detail 3: a packed array variable's vpiElement iteration collects
    // its subelement variables (struct/union/enum/packed-array vars), not
    // children whose own type is vpiElement.
    if (packed_array_var_element_iteration) {
      return VpiIsPackedArrayVarElementType(obj_type);
    }
    // §37.18 detail 6: a packed array variable's vpiIndex iteration collects the
    // index expressions locating a subelement within its parent.
    if (packed_array_var_index_iteration) return VpiIsExprType(obj_type);
    // §37.24 details 1 and 2: an interconnect array's vpiElement, an
    // interconnect net's vpiElement, and an interconnect net's vpiMember each
    // collect the interconnect subobjects they reach - a nested interconnect
    // array or a leaf interconnect net - not children whose own type is
    // literally vpiElement or vpiMember.
    if (interconnect_array_element_iteration ||
        interconnect_net_element_iteration ||
        interconnect_net_member_iteration) {
      return VpiIsInterconnectSubelementType(obj_type);
    }
    // §37.40 detail 2: a timing check's vpiExpr iteration collects its argument
    // objects - the reference/controlled-reference and data event terms (each a
    // vpiTchkTerm) together with the check's other argument expressions - rather
    // than children whose own type is literally vpiExpr.
    if (tchk_expr_iteration) {
      return obj_type == vpiTchkTerm || VpiIsExprType(obj_type);
    }
    // §37.72 detail 1: a case item's match expressions are reached through the
    // vpiExpr edge, which spans both patterns and plain expressions, so the
    // iteration collects every condition the item groups - not only children
    // whose own type happens to be vpiExpr.
    if (ref && ref->type == vpiCaseItem && type == vpiExpr) {
      return VpiIsCaseItemConditionType(obj_type);
    }
    // §37.42: a tf call's vpiArgument iteration collects its argument objects -
    // the exprs, interface exprs, scope, primitive, and named-event(-array) the
    // relation reaches - rather than children whose own type is vpiArgument.
    if (tf_argument_iteration) return VpiIsTfCallArgumentType(obj_type);
    // §37.34 detail 5: a constraint's vpiConstraintItem iteration collects every
    // constraint item it groups - the constraint orderings and constraint
    // expressions - in the order they occur, rather than children whose own type
    // is literally vpiConstraintItem.
    if (type == vpiConstraintItem) return VpiIsConstraintItemType(obj_type);
    return obj_type == type;
  };

  if (vif_iteration) {
    // §37.12 detail 7: the vpiVirtualInterfaceVar iteration is supported only in
    // an elaborated context; within a lexical context such as a class defn
    // (§37.31) it is not supported and yields nothing. Otherwise collect the
    // scope's virtual interface vars, expanding a declared array of virtual
    // interfaces into its individual elements.
    if (ref->type != vpiClassDefn) {
      for (auto* child : ref->children) {
        if (child->type == vpiVirtualInterfaceVar) {
          iter->children.push_back(child);
        } else if (VpiIsVirtualInterfaceArray(child)) {
          for (auto* elem : child->children) {
            if (elem->type == vpiVirtualInterfaceVar) {
              iter->children.push_back(elem);
            }
          }
        }
      }
    }
  } else if (variables_iteration) {
    // §37.12 detail 7: the scope's variables, with an array of virtual interfaces
    // reported as the single array var that declares it rather than expanded.
    for (auto* child : ref->children) {
      if (child->type == vpiVariables || VpiIsVirtualInterfaceArray(child)) {
        iter->children.push_back(child);
      }
    }
  } else if (import_iteration) {
    // §37.12 detail 4: the objects actually imported into the scope - those
    // referenced across an import declaration, marked imported.
    for (auto* child : ref->children) {
      if (child->imported) iter->children.push_back(child);
    }
  } else if (!ref && type == vpiUserSystf) {
    // §37.42 detail 6: every user-defined system task or function is retrieved
    // with vpi_iterate(vpiUserSystf, NULL). These are the registered systf
    // objects (callbacks marked as a system tf), found by that mark rather than
    // by a plain type match.
    for (auto* obj : all_objects_) {
      if (obj->is_systf) iter->children.push_back(obj);
    }
  } else if (!ref && type == vpiTimeQueue) {
    // §37.81: vpi_iterate(vpiTimeQueue, NULL) walks the simulation time queue.
    // Detail 3: the slot at the current simulation time takes part only when
    // events remain scheduled before its read-only synch region; a future slot
    // always contributes. Detail 1: the surviving slots are handed back in
    // increasing order of simulation time, so they are sorted by time here and
    // a time queue object carrying that time is produced for each. Detail 2 - an
    // empty queue yields NULL rather than an empty iterator - is left to the
    // shared empty-children check at the tail of this routine.
    std::vector<VpiTimeQueueSlot> slots;
    for (const auto& slot : time_queue_slots_) {
      if (slot.is_current && !slot.has_events_before_read_only_synch) continue;
      slots.push_back(slot);
    }
    std::sort(slots.begin(), slots.end(),
              [](const VpiTimeQueueSlot& a, const VpiTimeQueueSlot& b) {
                return a.time < b.time;
              });
    for (const auto& slot : slots) {
      auto* tq = AllocObject();
      tq->type = kVpiTimeQueue;
      tq->time_queue_time = slot.time;
      iter->children.push_back(tq);
    }
  } else if (net_driver_iteration || net_load_iteration) {
    // §37.46 (figure) + detail 1: collect the net's driver objects (vpiDriver) or
    // load objects (vpiLoad). On the load side a port is reported only when it
    // carries a complex, non-concatenation expression on an input - detail 1's
    // rule, applied inside the collector.
    CollectNetDriversOrLoads(ref, net_driver_iteration, iter);
  } else if (variable_driver_iteration || variable_load_iteration) {
    // §37.21 (figure): collect the variable's driver objects (vpiDriver) or load
    // objects (vpiLoad). §37.21 detail 1: for a structure, union, or class
    // variable the relation shall also include the drivers/loads of any
    // bit-select or part-select of the variable and of any member nested inside
    // it, so the walk descends through the variable's selects and members in that
    // case. Any other variable contributes only its own direct drivers/loads.
    CollectVariableDriversOrLoads(ref, variable_driver_iteration,
                                  VpiIsStructUnionOrClassVar(ref->type), iter);
  } else if (constr_foreach_loopvars_iteration ||
             foreach_stmt_loopvars_iteration) {
    // §37.38 detail 2 / §37.75 detail 2: hand back the foreach constraint's or
    // foreach statement's index variables in left-to-right order. A skipped index
    // position - stored as a null slot in the list - is reported as a freshly
    // built vpiOperation whose operator is the null operation, so the caller still
    // sees a placeholder occupying that slot (the same null-op convention §37.42
    // uses for an omitted argument).
    for (auto* loop_var : ref->loop_vars) {
      if (loop_var) {
        iter->children.push_back(loop_var);
      } else {
        VpiHandle placeholder = AllocObject();
        VpiMakeEmptyArgument(placeholder);
        iter->children.push_back(placeholder);
      }
    }
  } else if (constraint_expr_iteration) {
    // §37.38 detail 3: hand back the container's body constraint expressions in
    // the order they occur in the implication, if, if-else, or foreach.
    for (auto* expr : ref->constraint_exprs) {
      iter->children.push_back(expr);
    }
  } else if (ref) {
    for (auto* child : ref->children) {
      if (!matches(child->type)) continue;
      // §37.31 detail 1: the vpiMethods iteration omits implicit built-in methods
      // (those SystemVerilog provides with no explicit declaration); an explicitly
      // declared method, built-in or not, is still reported.
      if (class_methods_iteration && child->implicit_builtin_method) continue;
      // §37.31 detail 3: the vpiConstraint iteration returns only normal
      // constraints, so an inline constraint is left out.
      if (class_constraint_iteration && child->inline_constraint) continue;
      iter->children.push_back(child);
    }
  } else {
    for (auto* obj : all_objects_) {
      if (!matches(obj->type)) continue;
      // §37.5 detail 1: a NULL-reference vpiModule iteration reaches only the
      // top-level modules, never a module nested within another scope.
      if (top_module_iteration && !obj->top_module) continue;
      iter->children.push_back(obj);
    }
  }

  if (iter->children.empty()) {
    delete iter;
    return nullptr;
  }
  return iter;
}

VpiHandle VpiContext::Scan(VpiHandle iterator) {
  // §38.40: walk the objects an iterator (from vpi_iterate()) was built over,
  // handing back the next one on each call so the traversal advances one object
  // at a time. A null handle has nothing to traverse.
  if (!iterator) return nullptr;
  // §38.40: when the objects are exhausted there is nothing more to return.
  // Reporting NULL also retires the iterator handle - it is no longer valid and
  // must not be used again - so the storage is released here.
  if (iterator->scan_index >= iterator->children.size()) {
    delete iterator;
    return nullptr;
  }
  return iterator->children[iterator->scan_index++];
}

static void GetValueBinStr(VpiHandle obj, VpiValue* value,
                           std::vector<std::string>& pool) {
  uint64_t aval = obj->var->value.words[0].aval;
  uint64_t bval = obj->var->value.words[0].bval;
  int width = static_cast<int>(obj->var->value.width);
  std::string result;
  result.reserve(width);
  for (int i = width - 1; i >= 0; --i) {
    bool a_bit = (aval >> i) & 1;
    bool b_bit = (bval >> i) & 1;
    if (!b_bit) {
      result += (a_bit ? '1' : '0');
    } else {
      result += (a_bit ? 'z' : 'x');
    }
  }
  pool.push_back(std::move(result));
  value->value.str = pool.back().c_str();
}

static char HexDigitFromBits(uint8_t nibble) {
  if (nibble < 10) return static_cast<char>('0' + nibble);
  return static_cast<char>('a' + nibble - 10);
}

static void GetValueHexStr(VpiHandle obj, VpiValue* value,
                           std::vector<std::string>& pool) {
  uint64_t aval = obj->var->value.words[0].aval;
  uint64_t bval = obj->var->value.words[0].bval;
  int width = static_cast<int>(obj->var->value.width);
  int hex_digits = (width + 3) / 4;
  std::string result;
  result.reserve(hex_digits);
  for (int i = hex_digits - 1; i >= 0; --i) {
    uint8_t a_nibble = (aval >> (i * 4)) & 0xF;
    uint8_t b_nibble = (bval >> (i * 4)) & 0xF;
    if (b_nibble != 0) {
      result += (b_nibble == 0xF && a_nibble == 0xF) ? 'z' : 'x';
    } else {
      result += HexDigitFromBits(a_nibble);
    }
  }
  pool.push_back(std::move(result));
  value->value.str = pool.back().c_str();
}

static void GetValueOctStr(VpiHandle obj, VpiValue* value,
                           std::vector<std::string>& pool) {
  uint64_t aval = obj->var->value.words[0].aval;
  uint64_t bval = obj->var->value.words[0].bval;
  int width = static_cast<int>(obj->var->value.width);
  int oct_digits = (width + 2) / 3;
  std::string result;
  result.reserve(oct_digits);
  for (int i = oct_digits - 1; i >= 0; --i) {
    uint8_t a_bits = (aval >> (i * 3)) & 0x7;
    uint8_t b_bits = (bval >> (i * 3)) & 0x7;
    if (b_bits != 0) {
      // §38.15, Table 38-3 (octal row): a digit covering any unknown bit is
      // reported as z only when the whole group is z, otherwise as x.
      result += (b_bits == 0x7 && a_bits == 0x7) ? 'z' : 'x';
    } else {
      result += static_cast<char>('0' + a_bits);
    }
  }
  pool.push_back(std::move(result));
  value->value.str = pool.back().c_str();
}

static int ScalarFromBits(uint64_t aval, uint64_t bval) {
  if (!bval) return aval ? kVpi1 : kVpi0;
  return aval ? kVpiZ : kVpiX;
}

static void GetValueVector(VpiHandle obj, VpiValue* value,
                           std::vector<std::vector<VpiVectorVal>>& pool) {
  const auto& v = obj->var->value;
  int width = static_cast<int>(v.width);
  // §38.15: the vector value occupies an array of s_vpi_vecval whose size is
  // ((vector_size - 1) / 32 + 1), one element per 32 bits of the vector.
  int array_size = width > 0 ? ((width - 1) / 32 + 1) : 1;
  std::vector<VpiVectorVal> vec(static_cast<size_t>(array_size));
  for (int i = 0; i < array_size; ++i) {
    // Internal four-state words are 64 bits wide, so two vecval elements map
    // onto each word: the LSB of the vector lands in element 0, bit 33 in the
    // LSB of element 1, and so on.
    int word_idx = i / 2;
    int shift = (i % 2) * 32;
    uint64_t aval = word_idx < static_cast<int>(v.nwords)
                        ? v.words[word_idx].aval
                        : 0;
    uint64_t bval = word_idx < static_cast<int>(v.nwords)
                        ? v.words[word_idx].bval
                        : 0;
    auto a32 = static_cast<uint32_t>((aval >> shift) & 0xFFFFFFFFu);
    auto b32 = static_cast<uint32_t>((bval >> shift) & 0xFFFFFFFFu);
    // §38.15 / Figure 38-8: the returned encoding is ab 00=0, 10=1, 11=X,
    // 01=Z. That assigns the aval bit of an unknown the opposite sense from
    // the internal word (X is a=0/b=1, Z is a=1/b=1), so flip the aval bit of
    // every unknown position by xoring in the bval bits.
    vec[static_cast<size_t>(i)].aval = a32 ^ b32;
    vec[static_cast<size_t>(i)].bval = b32;
  }
  pool.push_back(std::move(vec));
  value->value.vector = pool.back().data();
}

static void GetValueStrength(VpiHandle obj, VpiValue* value,
                             std::vector<std::vector<VpiStrengthVal>>& pool) {
  const auto& v = obj->var->value;
  int width = static_cast<int>(v.width);
  if (width < 1) width = 1;
  // §38.15: the strength arm holds one descriptor per bit of the vector.
  std::vector<VpiStrengthVal> arr(static_cast<size_t>(width));
  for (int i = 0; i < width; ++i) {
    int word_idx = i / 64;
    int bit = i % 64;
    uint64_t aval =
        word_idx < static_cast<int>(v.nwords) ? v.words[word_idx].aval : 0;
    uint64_t bval =
        word_idx < static_cast<int>(v.nwords) ? v.words[word_idx].bval : 0;
    arr[static_cast<size_t>(i)].logic =
        ScalarFromBits((aval >> bit) & 1, (bval >> bit) & 1);
    // §38.15: a reg or variable is always reported at strong strength, so both
    // the 0 and 1 drive components carry the strong-drive code.
    arr[static_cast<size_t>(i)].s0 = vpiStrongDrive;
    arr[static_cast<size_t>(i)].s1 = vpiStrongDrive;
  }
  pool.push_back(std::move(arr));
  value->value.strength = pool.back().data();
}

static void GetValueStringVal(VpiHandle obj, VpiValue* value,
                              std::vector<std::string>& pool) {
  uint64_t val = obj->var->value.ToUint64();
  std::string s;
  for (int i = 56; i >= 0; i -= 8) {
    auto ch = static_cast<char>((val >> i) & 0xFF);
    if (ch != 0) s += ch;
  }
  pool.push_back(std::move(s));
  value->value.str = pool.back().c_str();
}

bool VpiExpressionHasSideEffects(const VpiObject* obj) {
  // §37.3.5: the mark records the classification described in the subclause; an
  // absent object cannot have side effects.
  return obj && obj->has_side_effects;
}

void VpiContext::GetValue(VpiHandle obj, VpiValue* value) {
  if (!obj || !value) return;
  // §37.3.5: applying vpi_get_value() to an expression with side effects shall
  // fully evaluate the expression together with its side effects. Reading the
  // value performs that evaluation, so record that the side effect occurred
  // before the value is handed back below - the count is the observable evidence
  // that evaluation, and thus the embedded state change, took place.
  if (VpiExpressionHasSideEffects(obj)) {
    ++obj->side_effect_count;
  }
  // §37.31 detail 2: vpi_get_value() is not allowed for variable and event
  // handles obtained from a class defn handle. Such a handle denotes a class
  // member rather than a free-standing object, so the read is refused, an error
  // is recorded, and the caller's value buffer is left untouched.
  if (obj->parent && obj->parent->type == vpiClassDefn &&
      VpiIsClassMemberValueType(obj->type)) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_get_value(): a variable or event handle obtained from a class "
        "definition handle has no accessible value";
    return;
  }
  // §37.26 detail 1: the value of an entire unpacked structure or unpacked
  // union is not accessible through vpi_get_value(). Such an aggregate holds no
  // single scalar or vector value to hand back, so the read is refused, an error
  // is recorded, and the caller's value buffer is left untouched. A packed
  // struct/union is excluded by the helper and reads normally.
  if (VpiIsEntireUnpackedStructOrUnion(obj->type, obj->packed)) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_get_value(): the value of an entire unpacked structure or union "
        "cannot be accessed";
    return;
  }
  if (!obj->var) return;
  switch (value->format) {
    case kVpiIntVal: {
      // §38.15, Table 38-3: any x or z bit of the object maps to a 0 in the
      // returned integer, so drop every unknown bit before handing it back.
      uint64_t aval = obj->var->value.words[0].aval;
      uint64_t bval = obj->var->value.words[0].bval;
      value->value.integer = static_cast<int>(aval & ~bval);
      break;
    }
    case kVpiRealVal:
      value->value.real = static_cast<double>(obj->var->value.ToUint64());
      break;
    case kVpiScalarVal:
      value->value.scalar = ScalarFromBits(obj->var->value.words[0].aval & 1,
                                           obj->var->value.words[0].bval & 1);
      break;
    case kVpiBinStrVal:
      GetValueBinStr(obj, value, str_pool_);
      break;
    case kVpiHexStrVal:
      GetValueHexStr(obj, value, str_pool_);
      break;
    case kVpiOctStrVal:
      GetValueOctStr(obj, value, str_pool_);
      break;
    case kVpiStringVal:
      GetValueStringVal(obj, value, str_pool_);
      break;
    case kVpiTimeVal:
      value->value.integer = static_cast<int>(obj->var->value.ToUint64());
      break;
    case kVpiVectorVal:
      GetValueVector(obj, value, vec_pool_);
      break;
    case kVpiStrengthVal:
      GetValueStrength(obj, value, strength_pool_);
      break;
    case kVpiObjTypeVal: {
      // §38.15: fill in the value and rewrite the format field to the closest
      // format for the object's type. A real object reports vpiRealVal, a
      // single-bit object is a scalar, and anything wider is a vector.
      const auto& v = obj->var->value;
      if (v.is_real) {
        value->format = kVpiRealVal;
        value->value.real = static_cast<double>(v.ToUint64());
      } else if (v.width == 1) {
        value->format = kVpiScalarVal;
        value->value.scalar =
            ScalarFromBits(v.words[0].aval & 1, v.words[0].bval & 1);
      } else {
        value->format = kVpiVectorVal;
        GetValueVector(obj, value, vec_pool_);
      }
      break;
    }
    default:
      break;
  }
}

VpiHandle VpiContext::PutValue(VpiHandle obj, VpiValue* value, VpiTime* time,
                               int flags) {
  if (!obj) return nullptr;

  // §37.31 detail 2: vpi_put_value() is not allowed for variable and event
  // handles obtained from a class defn handle, the write side of the same
  // restriction vpi_get_value() observes. The put is rejected, an error is
  // recorded, and the member is left unchanged.
  if (obj->parent && obj->parent->type == vpiClassDefn &&
      VpiIsClassMemberValueType(obj->type)) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_value(): a variable or event handle obtained from a class "
        "definition handle has no accessible value";
    return nullptr;
  }

  // §37.26 detail 1: an entire unpacked structure or union cannot be written
  // through vpi_put_value() any more than it can be read - it has no single
  // value to take the write. The put is rejected, an error is recorded, and the
  // aggregate is left unchanged. A packed struct/union is excluded by the helper
  // and is written through the normal path below.
  if (VpiIsEntireUnpackedStructOrUnion(obj->type, obj->packed)) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_value(): the value of an entire unpacked structure or union "
        "cannot be accessed";
    return nullptr;
  }

  // §37.35 detail 2: among primitives, vpi_put_value() may be applied only to a
  // sequential UDP. Putting a value to any other primitive kind - a gate,
  // switch, combinational UDP, or a generic primitive - is not allowed, so the
  // put is rejected before any value is written. (The complementary delay-mode
  // restriction on a sequential UDP itself is checked further below.)
  if (VpiObjectIsPrimitive(obj->type) && obj->type != vpiSeqPrim) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_value(): only a sequential UDP primitive may be written";
    return nullptr;
  }

  // §37.3.5: it is an error to apply vpi_put_value() to an object when any of
  // its index expressions has side effects (for instance my_array[i++] or
  // my_array[--i]). The write is rejected before any value is stored - an error
  // is recorded, the target is left unchanged, and the side-effecting index is
  // not evaluated.
  for (const VpiObject* index : obj->index_expressions) {
    if (VpiExpressionHasSideEffects(index)) {
      last_error_.state = kVpiError;
      last_error_.level = kVpiError;
      last_error_.message =
          "vpi_put_value(): an index expression with side effects is not "
          "allowed";
      return nullptr;
    }
  }

  // §38.34: vpiReturnEvent is an independent bit mask layered on top of the
  // delay-mode selector that lives in the low bits of the flags word.
  bool return_event = (flags & vpiReturnEvent) != 0;
  int mode = flags & ~vpiReturnEvent;

  // §38.34: vpiCancelEvent removes a previously scheduled event. The object
  // must be a vpiSchedEvent handle, and value_p and time_p are not needed. It
  // is not an error to cancel an event that has already occurred, so a handle
  // that is no longer scheduled is simply left alone. Cancelling removes the
  // event from the queue; the handle itself remains for the caller to free.
  if (mode == vpiCancelEvent) {
    if (obj->type == vpiSchedEvent) obj->scheduled = false;
    return nullptr;
  }

  // §38.34: vpiNoDelay, vpiForceFlag, and vpiReleaseFlag all act immediately and
  // ignore time_p; every other mode takes its delay from time_p, where a delay
  // is present when a nonzero time is supplied.
  bool immediate = (mode == vpiNoDelay || mode == vpiForceFlag ||
                    mode == vpiReleaseFlag);
  bool has_delay = !immediate && time &&
                   (time->low != 0 || time->high != 0 || time->real != 0.0);

  // §38.34: a sequential UDP is always set with no delay, no matter what delay
  // the primitive instance carries, so a value may be put to it only with the
  // vpiNoDelay flag. Supplying one of the scheduled delay modes instead is an
  // error, and the put is rejected.
  if (obj->type == vpiSeqPrim &&
      (mode == vpiInertialDelay || mode == vpiTransportDelay ||
       mode == vpiPureTransportDelay)) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_value(): a sequential UDP must be written with the vpiNoDelay "
        "flag";
    return nullptr;
  }

  // §37.43 detail 3: it is illegal to put a value with a delay on an automatic
  // variable. A delay would schedule the update for a future time, but the
  // automatic object's storage may no longer exist by then. Reject the put
  // rather than applying it.
  if (obj->automatic && has_delay) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_value(): a value with a delay may not be put on an automatic "
        "variable";
    return nullptr;
  }

  if (!obj->var && !obj->net) return nullptr;

  if (!obj->var) {
    if (scheduler_) scheduler_->NoteWriteAttempt();
    return nullptr;
  }

  // §38.34: putting to a vpiNamedEvent toggles (triggers) the named event. Such
  // an object needs no value, so value_p may be NULL and is not consulted.
  if (obj->var->is_event) {
    if (scheduler_)
      obj->var->triggered_ticks = scheduler_->CurrentTime().ticks;
    return nullptr;
  }

  if (!value) return nullptr;

  // §38.34: it is illegal to give the value the vpiStringVal format when the
  // target is a real object. Record the error and leave the object unchanged.
  if (value->format == kVpiStringVal && obj->var->value.is_real) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_value(): vpiStringVal is not a legal format for a real object";
    return nullptr;
  }

  // §38.34: it is illegal to give the value the vpiStrengthVal format when the
  // target is a vector object (more than one bit wide).
  if (value->format == kVpiStrengthVal && obj->var->value.width > 1) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_value(): vpiStrengthVal is not a legal format for a vector "
        "object";
    return nullptr;
  }

  // §38.34: vpiReleaseFlag releases a forced value, the same operation as the
  // procedural release of §10.6.2, and writes the object's post-release value
  // back through value_p so the caller can observe what the object settled to.
  if (mode == vpiReleaseFlag) {
    obj->var->is_forced = false;
    GetValue(obj, value);
    return nullptr;
  }

  if (scheduler_) scheduler_->NoteWriteAttempt();

  if (value->format == kVpiIntVal) {
    auto new_val = static_cast<uint64_t>(value->value.integer);
    obj->var->value.words[0].aval = new_val;
    obj->var->value.words[0].bval = 0;
  } else if (value->format == kVpiRealVal) {
    auto new_val = static_cast<uint64_t>(value->value.real);
    obj->var->value.words[0].aval = new_val;
    obj->var->value.words[0].bval = 0;
  } else if (value->format == kVpiScalarVal) {
    int s = value->value.scalar;
    obj->var->value.words[0].aval = (s == kVpi1 || s == kVpiZ) ? 1 : 0;
    obj->var->value.words[0].bval = (s == kVpiX || s == kVpiZ) ? 1 : 0;
  }

  // §38.34: vpiForceFlag performs a procedural force (§10.6.2): the supplied
  // value takes effect now and is held as the forced value.
  if (mode == vpiForceFlag) {
    obj->var->is_forced = true;
    obj->var->forced_value = obj->var->value;
  }

  // §38.34: a handle to the scheduled event is returned only when vpiReturnEvent
  // was requested and a delay actually scheduled an event; in every other case
  // (no bit mask, no delay, or nothing scheduled) the return value is NULL.
  if (return_event && has_delay) {
    auto* ev = AllocObject();
    ev->type = vpiSchedEvent;
    ev->scheduled = true;
    return ev;
  }
  return nullptr;
}

// §38.35: the value formats vpi_put_value_array() accepts. The int/vector/time/
// real forms are the vpi_get_value() formats reused from §38.15 (Table 38-3);
// the raw aval/bval forms and the short/long/short-real C-scalar forms are the
// additions §38.35 defines. Any other format is unsupported.
static bool VpiArrayPutFormatSupported(int format) {
  switch (format) {
    case kVpiIntVal:
    case kVpiVectorVal:
    case kVpiTimeVal:
    case kVpiRealVal:
    case kVpiShortIntVal:
    case kVpiLongIntVal:
    case kVpiShortRealVal:
    case kVpiRawTwoStateVal:
    case kVpiRawFourStateVal:
      return true;
    default:
      return false;
  }
}

// §38.35: read up to eight little-endian bytes of one raw aval (or bval) group
// into a 64-bit word. ngroups is (elemBits + 7)/8; the LSB of byte 0 is bit 0 of
// the element, the significance order the standard fixes for the avalbits and
// bvalbits arrays.
static uint64_t VpiReadRawGroup(const char* base, int ngroups) {
  uint64_t v = 0;
  for (int b = 0; b < ngroups && b < 8; ++b) {
    v |= static_cast<uint64_t>(static_cast<unsigned char>(base[b])) << (8 * b);
  }
  return v;
}

void VpiContext::PutValueArray(VpiHandle obj, VpiArrayValue* arrayvalue_p,
                               int* index_p, unsigned int num) {
  if (!obj || !arrayvalue_p) return;

  // §38.35: the routine modifies only static unpacked variable or net arrays -
  // arrays whose vpiArrayType is vpiStaticArray, which also have a static
  // lifetime and contain no dynamic array or dynamic element. A handle that is
  // not such an array has no element section to fill, so the call is rejected
  // and the error recorded (§38.2).
  bool is_unpacked_array =
      VpiIsArrayVarType(obj->type) || obj->type == vpiNetArray;
  if (!is_unpacked_array || obj->array_type != vpiStaticArray) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_value_array() requires a static unpacked array object";
    return;
  }

  // §38.35: vpiNoDelay is the only scheduling mode allowed here - the delay and
  // event modes of vpi_put_value() (§38.34) are not available. Only vpiOneValue
  // and vpiPropagateOff may accompany it (vpiNoDelay is the default, value 0 in
  // the flags word); any other flag bit is an error.
  const unsigned int kAllowed = kVpiOneValue | kVpiPropagateOff;
  if (arrayvalue_p->flags & ~kAllowed) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_value_array() allows only the vpiOneValue and vpiPropagateOff "
        "flags";
    return;
  }

  // §38.35: every format outside the supported set is unsupported and is an
  // error if specified.
  if (!VpiArrayPutFormatSupported(static_cast<int>(arrayvalue_p->format))) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_value_array() was given an unsupported value format";
    return;
  }

  // §38.35: index_p carries the starting element's coordinate, one entry per
  // unpacked dimension of obj, ordered left to right as the indices appear in an
  // HDL reference. With no coordinate there is no element to start from.
  const auto& dims = obj->array_dim_indices;
  if (index_p == nullptr || dims.empty()) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_value_array() requires a starting index for each unpacked "
        "dimension";
    return;
  }

  // §38.35: turn the starting coordinate into the flat ordinal of the first
  // element, with the rightmost dimension varying fastest - a mixed-radix value
  // over each dimension's declared index order. A coordinate value that names no
  // declared index is not a legal element reference.
  long long start_ordinal = 0;
  for (size_t d = 0; d < dims.size(); ++d) {
    const auto& order = dims[d];
    long long pos = -1;
    for (size_t p = 0; p < order.size(); ++p) {
      if (order[p] == index_p[d]) {
        pos = static_cast<long long>(p);
        break;
      }
    }
    if (pos < 0) {
      last_error_.state = kVpiError;
      last_error_.level = kVpiError;
      last_error_.message =
          "vpi_put_value_array() starting index is out of range";
      return;
    }
    start_ordinal = start_ordinal * static_cast<long long>(order.size()) + pos;
  }

  // §38.35: elements are filled consecutively in fastest-varying-index order,
  // which is exactly consecutive flat ordinals from the starting element. With
  // vpiOneValue the single supplied element value is applied to the whole
  // section, so the source position stays pinned at 0.
  bool one_value = (arrayvalue_p->flags & kVpiOneValue) != 0;
  for (unsigned int k = 0; k < num; ++k) {
    long long ordinal = start_ordinal + static_cast<long long>(k);
    VpiObject* element = nullptr;
    for (auto* child : obj->children) {
      if (child->index == ordinal) {
        element = child;
        break;
      }
    }
    if (!element || !element->var) continue;

    unsigned int src = one_value ? 0u : k;
    Logic4Vec& ev = element->var->value;
    uint32_t width = ev.width;
    uint64_t mask =
        (width >= 64) ? ~uint64_t{0} : ((uint64_t{1} << width) - 1);
    bool elem_4state = element->var->is_4state;
    uint64_t aval = 0;
    uint64_t bval = 0;

    switch (static_cast<int>(arrayvalue_p->format)) {
      case kVpiIntVal:
        aval = static_cast<uint64_t>(
            static_cast<uint32_t>(arrayvalue_p->value.integers[src]));
        break;
      case kVpiShortIntVal:
        aval = static_cast<uint64_t>(
            static_cast<uint16_t>(arrayvalue_p->value.shortints[src]));
        break;
      case kVpiLongIntVal:
        aval = static_cast<uint64_t>(arrayvalue_p->value.longints[src]);
        break;
      case kVpiRealVal:
        aval = static_cast<uint64_t>(arrayvalue_p->value.reals[src]);
        break;
      case kVpiShortRealVal:
        aval = static_cast<uint64_t>(arrayvalue_p->value.shortreals[src]);
        break;
      case kVpiTimeVal: {
        const VpiTime& t = arrayvalue_p->value.times[src];
        aval = (static_cast<uint64_t>(t.high) << 32) | t.low;
        break;
      }
      case kVpiVectorVal: {
        const VpiVectorVal& vv = arrayvalue_p->value.vectors[src];
        aval = vv.aval;
        bval = elem_4state ? vv.bval : 0;
        break;
      }
      case kVpiRawFourStateVal: {
        int ngroups = (static_cast<int>(width) + 7) / 8;
        const char* abase = arrayvalue_p->value.rawvals +
                            static_cast<size_t>(src) * ngroups * 2;
        aval = VpiReadRawGroup(abase, ngroups);
        // §38.35: when this 4-state format is used for a 2-state array, the
        // bvalbits group is ignored.
        bval = elem_4state ? VpiReadRawGroup(abase + ngroups, ngroups) : 0;
        break;
      }
      case kVpiRawTwoStateVal: {
        int ngroups = (static_cast<int>(width) + 7) / 8;
        const char* abase =
            arrayvalue_p->value.rawvals + static_cast<size_t>(src) * ngroups;
        aval = VpiReadRawGroup(abase, ngroups);
        // §38.35: this 2-state format carries no bvalbits; for a 4-state array
        // its bval bits are taken to be 0.
        bval = 0;
        break;
      }
      default:
        break;
    }

    if (ev.nwords > 0) {
      ev.words[0].aval = aval & mask;
      ev.words[0].bval = bval & mask;
    }
  }

  // §38.35: for a vpiArrayNet target the written values override the resolved
  // values of the named net elements and stay in effect until one of that
  // element's drivers next changes, when normal net resolution resumes. The
  // override is the write applied above; the re-resolution is a property of the
  // net solver, outside this routine. vpiPropagateOff, when set, suppresses
  // fanout notification of the change.
}

VpiHandle VpiContext::RegisterCb(VpiCbData* data) {
  if (!data) return nullptr;

  // §36.10.2: while VPI functionality is restricted - the startup phase, and
  // the sizetf phase after it that permits no additional access - a callback
  // may be registered only for the six early-phase reasons. Reject any other
  // reason rather than register a callback the phase does not allow.
  if (VpiPhaseRestrictsFunctionality(tool_phase_) &&
      !VpiStartupCallbackReasonAllowed(data->reason)) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_register_cb() may register only an early-phase callback reason "
        "while VPI functionality is restricted";
    return nullptr;
  }

  // §37.43 detail 2: it is illegal to place a value change callback on an
  // automatic variable - automatic storage exists only while its frame is
  // active, so there is no persistent object to watch. Reject the registration.
  if (data->reason == cbValueChange && data->obj && data->obj->automatic) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_register_cb(): a value change callback may not be placed on an "
        "automatic variable";
    return nullptr;
  }

  // §38.36.1: it is illegal to place a cbForce, cbRelease, or cbDisable
  // simulation-event callback on a variable bit-select. A single addressed bit
  // of a variable is not a legal target for a force/release/disable callback, so
  // reject the registration instead of handing back a callback that could never
  // fire correctly.
  if ((data->reason == cbForce || data->reason == cbRelease ||
       data->reason == cbDisable) &&
      data->obj && data->obj->type == vpiBitSelect) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_register_cb(): a cbForce, cbRelease, or cbDisable callback may not "
        "be placed on a variable bit-select";
    return nullptr;
  }

  // §38.36.2: a simulation-time callback carries its timing in the s_cb_data
  // time structure, and the standard constrains how that structure - and a
  // delay of zero - may be used. These checks apply only to the time-related
  // reasons; every other reason ignores the time field.
  if (VpiIsSimulationTimeCallbackReason(data->reason)) {
    // §38.36.2: the time->type field shall be vpiSimTime or vpiScaledRealTime.
    // A vpiSuppressTime type, or a null time pointer, leaves no time for the
    // callback to fire at, so registration is an error and no callback is made.
    if (data->time == nullptr || data->time->type == vpiSuppressTime) {
      last_error_.state = kVpiError;
      last_error_.level = kVpiError;
      last_error_.message =
          "vpi_register_cb(): a simulation-time callback requires a time "
          "structure with type vpiSimTime or vpiScaledRealTime";
      return nullptr;
    }

    // §38.36.2: the requested time, or the delay before the callback, lives in
    // time->{low,high,real}; a delay of zero is all three being zero.
    bool delay_is_zero = data->time->low == 0 && data->time->high == 0 &&
                         data->time->real == 0.0;

    // §38.36.2: a zero-delay cbAtStartOfSimTime callback may not be placed once
    // simulation has progressed into a time slice - unless the application is
    // itself running inside a cbAtStartOfSimTime callback, where it is allowed
    // and produces another cbAtStartOfSimTime callback in the same time slice.
    if (data->reason == cbAtStartOfSimTime && delay_is_zero &&
        sim_progressed_into_time_slice_ &&
        current_callback_reason_ != cbAtStartOfSimTime) {
      last_error_.state = kVpiError;
      last_error_.level = kVpiError;
      last_error_.message =
          "vpi_register_cb(): a zero-delay cbAtStartOfSimTime callback may not "
          "be placed after simulation has entered a time slice, except from "
          "within a cbAtStartOfSimTime callback";
      return nullptr;
    }

    // §38.36.2: a zero-delay cbReadWriteSynch callback may not be placed at
    // read-only synch time, where scheduling an event for the current time is
    // not permitted.
    if (data->reason == cbReadWriteSynch && delay_is_zero &&
        at_read_only_synch_time_) {
      last_error_.state = kVpiError;
      last_error_.level = kVpiError;
      last_error_.message =
          "vpi_register_cb(): a zero-delay cbReadWriteSynch callback may not be "
          "placed at read-only synch time";
      return nullptr;
    }
  }

  callbacks_.push_back(*data);

  auto* cb_obj = AllocObject();
  cb_obj->type = kVpiCallback;
  cb_obj->index = static_cast<int>(callbacks_.size() - 1);
  cb_handles_.push_back(cb_obj);
  return cb_obj;
}

int VpiContext::RemoveCb(VpiHandle cb_handle) {
  // §38.39: the argument shall be a handle to the callback object. A null or
  // wrong-typed handle is not a callback object, so removal fails.
  if (!cb_handle) return 0;
  if (cb_handle->type != kVpiCallback) return 0;
  int idx = cb_handle->index;
  if (idx >= 0 && idx < static_cast<int>(callbacks_.size())) {
    // §38.39: once vpi_remove_cb() has been called with a handle to the
    // callback, that handle is no longer valid. A cleared reason marks an
    // already-removed slot, so a repeat removal on the stale handle fails
    // rather than reporting success a second time.
    if (callbacks_[idx].reason < 0) return 0;
    callbacks_[idx].reason = -1;
    return 1;
  }
  return 0;
}

int VpiContext::ExecuteCallback(VpiHandle cb_handle) {
  if (!cb_handle || cb_handle->type != kVpiCallback) return 0;
  int idx = cb_handle->index;
  if (idx < 0 || idx >= static_cast<int>(callbacks_.size())) return 0;
  VpiCbData& cb = callbacks_[idx];
  // §38.36: the simulator executes the callback by invoking the cb_rtn the
  // application supplied, passing it a pointer to the s_cb_data structure (which
  // belongs to the simulator). With no cb_rtn there is nothing to invoke.
  if (!cb.cb_rtn) return 0;
  return cb.cb_rtn(&cb);
}

void VpiContext::RegisterCbValueChange(const VpiCbData& data) {
  if (!data.obj || !data.obj->var) return;
  void* user_data = data.user_data;
  data.obj->var->AddWatcher([user_data]() {
    if (user_data) *static_cast<bool*>(user_data) = true;
    return true;
  });
}

int VpiContext::DispatchCallbacks(int reason, VpiHandle obj, void* user_data) {
  int fired = 0;
  // §38.36.3: only callbacks still registered for this reason are delivered.
  // RemoveCb marks a removed callback by clearing its reason, so a removed slot
  // never matches a real reason here. Snapshot the count so callbacks registered
  // from within a routine are not delivered during this same pass.
  size_t count = callbacks_.size();
  for (size_t i = 0; i < count; ++i) {
    if (callbacks_[i].reason != reason || callbacks_[i].cb_rtn == nullptr) {
      continue;
    }
    // §38.36.3: the routine is passed a pointer to an s_cb_data structure that
    // is not the one supplied at registration. Work from a copy and let the
    // simulator fill obj/user_data when it has them for this reason.
    VpiCbData data = callbacks_[i];
    if (obj != nullptr) {
      data.obj = obj;
    }
    if (user_data != nullptr) {
      data.user_data = user_data;
    }
    // §38.9: record the reason of the routine about to run so that a routine
    // gated on its callback reason (e.g. vpi_get_data, legal only under
    // cbStartOfRestart/cbEndOfRestart) can observe it. Restore the prior value
    // afterward to keep nested dispatches honest.
    int saved_reason = current_callback_reason_;
    current_callback_reason_ = data.reason;
    data.cb_rtn(&data);
    current_callback_reason_ = saved_reason;
    ++fired;
  }
  return fired;
}

int VpiContext::DispatchReset() {
  int fired = DispatchCallbacks(kCbStartOfReset);
  fired += DispatchCallbacks(kCbEndOfReset);
  return fired;
}

int VpiContext::DispatchRestart() {
  // §37.2.2 (restart): a simulation restart releases all handles except the
  // handles to the cbStartOfRestart and cbEndOfRestart callbacks. Apply this
  // before the callback reasons are cleared below, so the surviving restart
  // callbacks are still identifiable by their reason.
  ReleaseHandlesForRestart();

  // §38.36.3: with the exception of the restart callbacks, every registered
  // callback is removed when a restart occurs. Clearing the reason marks a slot
  // removed, matching RemoveCb.
  for (VpiCbData& slot : callbacks_) {
    if (slot.reason != kCbStartOfRestart && slot.reason != kCbEndOfRestart) {
      slot.reason = -1;
    }
  }
  int fired = DispatchCallbacks(kCbStartOfRestart);
  fired += DispatchCallbacks(kCbEndOfRestart);
  return fired;
}

int VpiContext::SmallestModuleTimePrecision() const {
  // §37.10 detail 7: gather the precision of every module in the design and
  // return the smallest one.
  std::vector<int> precisions;
  for (const VpiObject* candidate : all_objects_) {
    if (candidate->type == kVpiModule) {
      precisions.push_back(candidate->time_precision);
    }
  }
  return VpiSmallestTimePrecision(precisions);
}

int VpiContext::Get(int property, VpiHandle obj) {
  // §37.10 detail 7: a null handle paired with a time property is a query for
  // the design-wide smallest time precision of all modules, for both
  // vpiTimePrecision and vpiTimeUnit.
  if (!obj) {
    if (property == vpiTimePrecision || property == vpiTimeUnit) {
      return SmallestModuleTimePrecision();
    }
    return 0;
  }
  // §37.3.6: unless otherwise specified, asking vpi_get() for a property of a
  // protected object is an error - it represents code sealed in a decryption
  // envelope. Access to the vpiType and vpiIsProtected properties is the stated
  // exception: it shall be permitted for all objects, so those two are let
  // through to the switch below while every other property records the error and
  // returns vpiUndefined, the value vpi_get() yields whenever an error occurs.
  // §37.59 detail 8 carves out one more case: a protected *expression* shall
  // still permit access to vpiSize, so that property passes through too when the
  // object is one of the expr-class kinds.
  if (obj->is_protected && property != kVpiType && property != vpiIsProtected &&
      !(property == kVpiSize && VpiIsExprType(obj->type))) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message = "vpi_get() on a protected object is an error";
    return vpiUndefined;
  }
  // §37.3.5: it is an error to ask for a property of an expression when the
  // implementation cannot determine that property without also evaluating an
  // expression that has side effects (for instance the vpiSize of a function
  // call that cannot be sized without calling it). The query is refused rather
  // than silently triggering the side effect. The object's kind is always
  // available structurally, so vpiType is let through; every other property
  // records the error and returns vpiUndefined, the value vpi_get() yields on
  // error.
  if (obj->property_needs_side_effect_eval && property != kVpiType) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_get(): this property cannot be determined without evaluating an "
        "expression with side effects";
    return vpiUndefined;
  }
  switch (property) {
    case kVpiType:
      return obj->type;
    // §37.3.6: every object carries a vpiIsProtected Boolean property (not drawn
    // in the data model diagrams) reporting whether the handle denotes protected
    // code; TRUE when protected, FALSE otherwise.
    case vpiIsProtected:
      return obj->is_protected ? 1 : 0;
    // §37.33 detail 1: a class object reports its own unique identifier. §37.33
    // detail 2: a class variable reports the identifier of the object it
    // currently references, or 0 when it references no object (it holds null).
    // The identifier is a 64-bit value; tiny identifiers are returned as-is.
    case vpiObjId:
      if (obj->type == vpiClassVar) {
        return obj->referenced_object
                   ? static_cast<int>(obj->referenced_object->obj_id)
                   : 0;
      }
      return static_cast<int>(obj->obj_id);
    case kVpiSize:
      // §37.85 detail 1: a gen scope array reports the number of elements in the
      // array - the gen scopes it holds - rather than any stored width.
      if (obj->type == vpiGenScopeArray) return VpiGenScopeArraySize(obj);
      // §37.47 detail 1: a cont assign bit models a single bit of a continuous
      // assignment, so its size is always scalar (one) regardless of any stored
      // width.
      if (obj->type == vpiContAssignBit) return 1;
      // §37.14 detail 11: a null port reports size 0; any other port reports its
      // bit width. Every other object reports its own stored size. §37.35 detail
      // 1: for a primitive that stored size is its number of inputs, so vpiSize
      // returns the input count through this same path.
      if (obj->type == vpiPort) return VpiPortSize(obj->null_port, obj->size);
      return obj->size;
    // §37.35 detail 3: a prim term reports its terminal index through
    // vpiTermIndex, which fixes the terminal order; the first terminal carries
    // index zero.
    case vpiTermIndex:
      return obj->index;
    case kVpiDirection:
      return obj->direction;
    // §37.14 detail 1: a port reports its port type (vpiPort/vpiInterfacePort/
    // vpiModportPort), fixed by the formal.
    case vpiPortType:
      return obj->port_type;
    // §37.14 detail 6: a port reports whether it is scalar (exactly one bit) or a
    // vector (more than one bit), based on its own width.
    case vpiScalar:
      if (obj->type == vpiPort) return VpiPortScalar(obj->size) ? 1 : 0;
      return 0;
    case vpiVector:
      if (obj->type == vpiPort) return VpiPortVector(obj->size) ? 1 : 0;
      return 0;
    // §37.14 detail 8: whether a port carries an explicit name.
    case vpiExplicitName:
      return obj->explicit_name ? 1 : 0;
    // §37.14 details 7 and 9: the port index gives port order (the first port is
    // 0); it does not apply to a port bit, which reports vpiUndefined.
    case vpiPortIndex:
      if (obj->type == vpiPortBit) return vpiUndefined;
      return obj->index;
    // §37.15 detail 5: a ref obj reports whether it refers to a generic interface
    // (TRUE/FALSE for an interface reference, vpiUndefined for any other ref obj).
    case vpiGeneric: {
      if (obj->type != vpiRefObj) return vpiUndefined;
      bool refers_to_interface =
          obj->actual && (obj->actual->type == vpiInterface ||
                          obj->actual->type == vpiInterfaceArray);
      return VpiRefObjGeneric(refers_to_interface, obj->generic_interface);
    }
    // §37.30: an interface typespec reports whether it represents a modport
    // (rather than the interface itself) as the vpiIsModPort Boolean property.
    case vpiIsModPort:
      return obj->is_modport ? 1 : 0;
    // §37.5: a module reports whether it is a top-level module - one reached by
    // iterating vpiModule with a NULL reference - through the vpiTopModule
    // Boolean property.
    case vpiTopModule:
      return obj->top_module ? 1 : 0;
    // §37.84: an iterator reports the kind of object its iteration walks - the
    // type code it was created to traverse - through the integer vpiIteratorType
    // property. A non-iterator object has no walked kind, so it reports 0.
    case vpiIteratorType:
      return obj->iter_type;
    // §37.5: a module reports its default net decay time (in time units) through
    // the vpiDefDecayTime integer property.
    case vpiDefDecayTime:
      return obj->def_decay_time;
    // §37.28: a parameter reports whether it is a localparam through the
    // vpiLocalParam Boolean property.
    case vpiLocalParam:
      return obj->local_param ? 1 : 0;
    // §37.28: a param assign reports whether the override connects by name (as
    // opposed to by position) through the vpiConnByName Boolean property.
    case vpiConnByName:
      return obj->conn_by_name ? 1 : 0;
    // §37.3.7: declared lifetime as a Boolean (0 static, 1 non-static).
    case kVpiAutomatic:
      return obj->automatic ? 1 : 0;
    // §37.3.7: the object's allocation scheme; defaults to kVpiOtherScheme.
    case kVpiAllocScheme:
      // §37.61 detail 2: an object reached through a class var or virtual
      // interface var prefix shares that prefix's memory allocation scheme, so
      // report the prefix's scheme rather than the object's own. A clocking-
      // block prefix is not subject to this rule, nor is an unprefixed object.
      if (obj->prefix && (obj->prefix->type == vpiClassVar ||
                          obj->prefix->type == vpiVirtualInterfaceVar)) {
        return obj->prefix->alloc_scheme;
      }
      return obj->alloc_scheme;
    // §37.54 (D2): an operation reports its operation type as an int property.
    case vpiOpType:
      return obj->op_type;
    // §37.62: an event statement reports through vpiBlocking whether it is a
    // blocking event trigger (->) as opposed to a nonblocking one (->>). The
    // property is drawn only on the event statement object, so asking any other
    // object kind is not a valid query and yields vpiUndefined; for an event
    // statement the answer is the stored Boolean, reported as 1 or 0.
    case vpiBlocking:
      if (obj->type != vpiEventStmt) return vpiUndefined;
      return obj->blocking ? 1 : 0;
    // §37.83: an attribute reports through vpiDefAttribute whether it was specified
    // on a definition rather than on an instance. The property is drawn only on the
    // attribute object, so asking any other object kind is not a valid query and
    // yields vpiUndefined; for an attribute the answer is the stored Boolean.
    case vpiDefAttribute:
      if (obj->type != vpiAttribute) return vpiUndefined;
      return obj->def_attribute ? 1 : 0;
    // §37.83: an attribute reports the source line of its definition through the
    // vpiDefLineNo integer property, again drawn only on the attribute object.
    case vpiDefLineNo:
      if (obj->type != vpiAttribute) return vpiUndefined;
      return obj->def_line_no;
    // §37.63 detail 1: a process reports which kind of always procedure it is
    // through vpiAlwaysType, restricted to vpiAlways/vpiAlwaysComb/vpiAlwaysFF/
    // vpiAlwaysLatch. A process carrying none of those - an initial or final
    // process, or an unset always_type - has no always type, so the property
    // reports vpiUndefined rather than handing back a value outside the four.
    case vpiAlwaysType:
      return VpiIsAlwaysType(obj->always_type) ? obj->always_type : vpiUndefined;
    // §37.61 detail 3: a dynamically prefixed object reports through vpiHasActual
    // whether it has a corresponding actual. The property is drawn only on the
    // dynamic-prefix source kinds, so asking any other object kind is not a valid
    // query and yields vpiUndefined; for a source kind the answer follows the
    // object's provenance (and, when that leaves it open, whether an actual is
    // bound at the current simulation time).
    case vpiHasActual:
      if (!VpiIsDynamicPrefixSourceType(obj->type)) return vpiUndefined;
      return VpiObjectHasActual(obj->actual_origin, obj->actual != nullptr) ? 1
                                                                            : 0;
    // §37.72: a case statement reports its case kind (vpiCaseExact/vpiCaseX/
    // vpiCaseZ) as an int property.
    case vpiCaseType:
      return obj->case_type;
    // §37.72: a case statement reports its qualifier flags (a bitwise OR of the
    // unique/priority/etc. qualifiers, vpiNoQualifier when none) as an int
    // property.
    case vpiQualifier:
      return obj->qualifier;
    // §37.59: a constant reports its constant type as an int property
    // (vpiUnboundedConst for the $ used in assertion ranges, detail 4); an unset
    // constant reports zero.
    case vpiConstType:
      return obj->const_type;
    // §37.59: an indexed part-select reports its index-part-select type (the
    // direction of the +:/-: selection) as an int property; zero when unset.
    case vpiIndexedPartSelectType:
      return obj->indexed_part_select_type;
    // §37.52 detail 3: an operation reports whether it is the strong version of
    // its operator as a Boolean property (TRUE for the strong form).
    case vpiOpStrong:
      return obj->op_strong ? 1 : 0;
    // §37.43/§37.44: a frame or a thread reports whether it is the active one as
    // a Boolean property (the same vpiActive property, shared by both models).
    case vpiActive:
      return obj->active ? 1 : 0;
    // §38.34: a scheduled-event handle reports whether its event is still in the
    // event queue as a Boolean property; cancelling the event clears it.
    case vpiScheduled:
      return obj->scheduled ? 1 : 0;
    // §37.50: a cover reports whether it covers a sequence (rather than a
    // property) as a Boolean property.
    case vpiIsCoverSequence:
      return obj->cover_sequence ? 1 : 0;
    // §37.50 (detail 1): a concurrent assertion reports whether its clocking
    // event was inferred (rather than explicit) as a Boolean property.
    case vpiIsClockInferred:
      return obj->clock_inferred ? 1 : 0;
    // §37.55: an immediate assertion (immediate assert/assume/cover) reports
    // whether it is a deferred assertion and whether it is a final assertion as
    // Boolean properties. Both are drawn only on the immediate-assertion kinds,
    // so asking any other object kind is not a valid query and yields
    // vpiUndefined.
    case vpiIsDeferred:
      if (!VpiIsImmediateAssertionType(obj->type)) return vpiUndefined;
      return obj->is_deferred ? 1 : 0;
    case vpiIsFinal:
      if (!VpiIsImmediateAssertionType(obj->type)) return vpiUndefined;
      return obj->is_final ? 1 : 0;
    // §6.9.2: the advisory vector-net accessibility keywords, reported as
    // Boolean properties. vpiExplicitScalared/vpiExplicitVectored each report
    // whether that keyword was written on the declaration. vpiExpanded reports
    // whether the PLI treats the net as expanded: a scalared net shall be
    // expanded, while a vectored net is reported unexpanded; a net declared
    // with neither keyword defaults to expanded.
    case vpiExplicitScalared:
      return obj->is_scalared ? 1 : 0;
    case vpiExplicitVectored:
      return obj->is_vectored ? 1 : 0;
    // §37.16 detail 21: vpiExpanded on a net bit reports the parent net's value;
    // otherwise it reports the object's own expansion (a scalared net, and the
    // default, is expanded; a vectored net is not).
    case vpiExpanded:
      if (obj->type == vpiNetBit) return VpiNetBitExpanded(obj) ? 1 : 0;
      return obj->is_vectored ? 0 : 1;
    // §37.16 detail 9: whether a net was created by implicit declaration.
    case vpiImplicitDecl:
      return obj->implicit_decl ? 1 : 0;
    // §37.49: the integer components of an assertion's source span.
    case vpiStartLine:
      return obj->start_line;
    case vpiColumn:
      return obj->column;
    case vpiEndLine:
      return obj->end_line;
    case vpiEndColumn:
      return obj->end_column;
    // §37.3.3: vpiLineNo reports the source line an object occupies. It applies
    // to every object that corresponds to source text; for the object kinds
    // §37.3.3 excepts (which have no single source line) it is not a valid query
    // and yields vpiUndefined.
    case vpiLineNo:
      if (!VpiHasLocationProperties(obj->type)) return vpiUndefined;
      return obj->line_no;
    // §37.47 detail 3: a cont assign bit reports its bit offset from the least
    // significant bit through vpiOffset. The offset is measured from the LSB, so
    // the LSB shall report zero - exactly the default this field holds.
    case vpiOffset:
      return obj->offset;
    // §37.47: a continuous assignment reports whether it is a net declaration
    // assignment through the vpiNetDeclAssign Boolean property.
    case vpiNetDeclAssign:
      return obj->net_decl_assign ? 1 : 0;
    // §37.47: a continuous assignment reports the drive strengths on its 0 and 1
    // values through vpiStrength0 and vpiStrength1.
    case vpiStrength0:
      return obj->strength0;
    case vpiStrength1:
      return obj->strength1;
    // §37.34 detail 3: a constraint's access type is vpiExternAcc when it is
    // declared outside its enclosing class declaration, and zero otherwise -
    // the only two values the property takes for a constraint. Any other stored
    // value collapses to zero so the constraint never reports a third value.
    case vpiAccessType:
      if (obj->type == vpiConstraint)
        return obj->access_type == vpiExternAcc ? vpiExternAcc : 0;
      // §37.8 detail 2: an interface task or function declaration reports an
      // access type that is only ever vpiForkJoinAcc or vpiExternAcc. Any other
      // stored value is not a legal access type here, so it collapses to
      // vpiUndefined rather than letting a third value escape the property.
      if (obj->type == vpiInterfaceTfDecl)
        return (obj->access_type == vpiForkJoinAcc ||
                obj->access_type == vpiExternAcc)
                   ? obj->access_type
                   : vpiUndefined;
      // §37.41 detail 6: a DPI ("DPI" or "DPI-C") task or function reports
      // vpiDPIExportAcc when it is an export and vpiDPIImportAcc when it is an
      // import. A non-DPI task or function falls through to its stored access type.
      if ((obj->type == vpiFunction || obj->type == vpiTask) && obj->is_dpi)
        return obj->dpi_export ? vpiDPIExportAcc : vpiDPIImportAcc;
      return obj->access_type;
    // §37.41 detail 7: vpiDPIPure reports TRUE for a pure DPI import function and
    // FALSE otherwise - the value of the stored flag, which is set only for such a
    // function.
    case vpiDPIPure:
      return obj->dpi_pure ? 1 : 0;
    // §37.41 detail 8: vpiDPIContext reports TRUE for a context import DPI task or
    // function and FALSE otherwise.
    case vpiDPIContext:
      return obj->dpi_context ? 1 : 0;
    // §37.41 detail 9: vpiDPICStr reports vpiDPIC for a "DPI-C" task or function
    // and vpiDPI for a "DPI" task or function. A task or function that is not a DPI
    // tf carries no such flavor, so the property is meaningful only when is_dpi is
    // set; report zero (none) otherwise.
    case vpiDPICStr:
      if (!obj->is_dpi) return 0;
      return obj->is_dpi_c ? vpiDPIC : vpiDPI;
    // §37.34: whether a constraint is virtual, as a Boolean property.
    case vpiVirtual:
      return obj->is_virtual ? 1 : 0;
    // §37.34: whether a constraint is currently enabled, as a Boolean property.
    case vpiIsConstraintEnabled:
      return obj->constraint_enabled ? 1 : 0;
    // §37.34: the distribution kind a dist item carries, as an int property.
    case vpiDistType:
      return obj->dist_type;
    // §37.26 (figure): a structure or union object reports whether it is packed
    // as the vpiPacked Boolean property (TRUE for a packed aggregate). Any
    // object not declared packed reports FALSE.
    case vpiPacked:
      return obj->packed ? 1 : 0;
    // §37.26 (figure): a union object reports whether it is a tagged union as
    // the vpiTagged Boolean property.
    case vpiTagged:
      return obj->tagged ? 1 : 0;
    // §37.26 (figure): a packed union reports whether it is a soft-packed union
    // as the vpiSoft Boolean property.
    case vpiSoft:
      return obj->soft ? 1 : 0;
    // §37.12 detail 6: a fork-join scope reports the kind of join that
    // terminates it through vpiJoinType, restricted to vpiJoin/vpiJoinNone/
    // vpiJoinAny. A stored value outside those three is not a join type, so the
    // property collapses to vpiJoin (the plain join) rather than escaping a
    // fourth value.
    case vpiJoinType:
      return VpiIsJoinType(obj->join_type) ? obj->join_type : vpiJoin;
    // §37.12 detail 2: a for statement reports whether it declares its loop
    // control variables local to the loop through the vpiLocalVarDecls Boolean
    // property; this is exactly the condition under which the for statement is a
    // scope.
    case vpiLocalVarDecls:
      return obj->local_var_decls ? 1 : 0;
    // §37.45: a delay device and a delay term both report the kind of delay they
    // model through the vpiDelayType integer property. The value is the stored
    // delay-type code; objects that are neither carry zero and so report zero.
    case vpiDelayType:
      return obj->delay_type;
    default:
      return 0;
  }
}

// §37.3.2: vpi_get_str(vpiType, ...) hands back the name of the type constant,
// and that name is derived from the object's name in the data model diagram
// (§37.3) - i.e. it is the very identifier of the type constant. This maps the
// object-type codes the simulator models onto those spellings; an unmodelled
// type yields no name (null), leaving room for other subclauses' types.
static const char* VpiTypeConstantName(int type) {
  switch (type) {
    case vpiModule:
      return "vpiModule";
    // §37.16 details 27 and 29: vpiLogicNet is #defined the same as vpiNet and
    // vpiArrayNet the same as vpiNetArray, so vpi_get_str(vpiType) may report
    // either spelling for those kinds. The simulator returns the IEEE 1364 net
    // spellings, which are among the permitted names.
    case vpiNet:  // == vpiLogicNet
      return "vpiNet";
    case vpiNetArray:  // == vpiArrayNet
      return "vpiNetArray";
    case vpiNetBit:
      return "vpiNetBit";
    case vpiStructNet:
      return "vpiStructNet";
    case vpiUnionNet:
      return "vpiUnionNet";
    case vpiEnumNet:
      return "vpiEnumNet";
    case vpiIntegerNet:
      return "vpiIntegerNet";
    case vpiTimeNet:
      return "vpiTimeNet";
    case vpiBitNet:
      return "vpiBitNet";
    case vpiPackedArrayNet:
      return "vpiPackedArrayNet";
    case vpiInterconnectNet:
      return "vpiInterconnectNet";
    case vpiInterconnectArray:
      return "vpiInterconnectArray";
    case vpiReg:
      return "vpiReg";
    case vpiPort:
      return "vpiPort";
    case vpiParameter:
      return "vpiParameter";
    case vpiConstant:
      return "vpiConstant";
    case vpiNamedEvent:
      return "vpiNamedEvent";
    case vpiOperation:
      return "vpiOperation";
    case vpiPrimitive:
      return "vpiPrimitive";
    case vpiIterator:
      return "vpiIterator";
    case vpiTypespec:
      return "vpiTypespec";
    case vpiFrame:
      return "vpiFrame";
    case vpiThread:
      return "vpiThread";
    case kVpiCallback:
      return "vpiCallback";
    case kVpiTimeQueue:
      return "vpiTimeQueue";
    default:
      return nullptr;
  }
}

const char* VpiContext::GetStr(int property, VpiHandle obj) {
  // §38.11: vpi_get_str() returns string property values. The value is placed in
  // a single temporary buffer reused by every call - so a pointer from an
  // earlier call is overwritten by the next - and that buffer is distinct from
  // str_pool_, the storage for s_vpi_value strings. A null raw result (null or
  // protected object, or a property with no string) yields null, not "".
  const char* raw = GetStrRaw(property, obj);
  if (!raw) return nullptr;
  // Reserve once so repeated assigns of typical-length strings keep writing into
  // the same allocation, leaving an earlier returned pointer valid until the
  // next call overwrites its contents.
  if (get_str_buffer_.capacity() < 256) get_str_buffer_.reserve(256);
  get_str_buffer_.assign(raw);
  return get_str_buffer_.c_str();
}

const char* VpiContext::GetStrRaw(int property, VpiHandle obj) {
  if (!obj) return nullptr;
  // §37.3.6: a protected object's properties are inaccessible unless otherwise
  // specified, so a string query for one is an error. The vpiType and
  // vpiIsProtected properties are the exception - permitted for all objects - so
  // they fall through; any other property records the error and yields no string.
  if (obj->is_protected && property != kVpiType && property != vpiIsProtected) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message = "vpi_get_str() on a protected object is an error";
    return nullptr;
  }
  switch (property) {
    // §37.3.2: every object carries a vpiType property; queried as a string it
    // yields the name of that type constant (see 37.3 for how the names derive).
    case kVpiType:
      return VpiTypeConstantName(obj->type);
    case kVpiName:
      // §37.14 detail 7: vpiName does not apply to a port bit.
      if (obj->type == vpiPortBit) return nullptr;
      // §37.14 detail 8: a port returns its name - explicit name preferred, then
      // any inferred name, else NULL. The model stores one name, so an unnamed
      // (null) port yields NULL while a named port yields its name.
      if (obj->type == vpiPort) {
        return VpiPortName(obj->explicit_name, obj->name.data(),
                           obj->name.data());
      }
      // §37.60 detail 1: an atomic statement's vpiName is its label when one was
      // written, and NULL otherwise - never an empty string for an unlabeled
      // statement.
      if (VpiIsAtomicStmtType(obj->type)) {
        return obj->name.empty() ? nullptr : obj->name.data();
      }
      return obj->name.data();
    // §37.3.3: vpiFile names the source file an object came from - one of the two
    // location properties, alongside vpiLineNo. It applies to every object that
    // corresponds to source text; the object kinds §37.3.3 excepts have no source
    // file and yield null regardless of any stored string. The `line directive
    // (§22.12) may shift the reported file. §37.49 stores an assertion's file in
    // the same field, and it is handed back here.
    case vpiFile:
      if (!VpiHasLocationProperties(obj->type)) return nullptr;
      return obj->file.empty() ? nullptr : obj->file.c_str();
    // §37.83: an attribute reports the source file of its definition through the
    // vpiDefFile string property. It is drawn only on the attribute object; an
    // attribute with no recorded definition file - and any other object kind -
    // yields null rather than an empty string.
    case vpiDefFile:
      if (obj->type != vpiAttribute) return nullptr;
      return obj->def_file.empty() ? nullptr : obj->def_file.c_str();
    case kVpiFullName:
      return obj->full_name.empty() ? obj->name.data() : obj->full_name.c_str();
    // §37.41 detail 10: vpiDPICIdentifier reports the C linkage name of a "DPI" or
    // "DPI-C" task or function. An object that carries no such name yields null
    // rather than an empty string.
    case vpiDPICIdentifier:
      return obj->dpi_c_identifier.empty() ? nullptr
                                           : obj->dpi_c_identifier.c_str();
    case kVpiDefName:
      if (obj->type == kVpiModule) return obj->name.data();
      // §37.15 detail 6: a ref obj whose actual is an interface or modport
      // reports that interface's definition name or the modport name.
      if (obj->type == vpiRefObj) return VpiRefObjDefName(obj);
      // §37.30 detail 1: an interface typespec reports the modport identifier or
      // the interface declaration's identifier as its definition name.
      if (obj->type == vpiInterfaceTypespec) {
        return VpiInterfaceTypespecDefName(obj);
      }
      return nullptr;

    case kVpiLibrary:
      if (obj->type != kVpiModule) return nullptr;
      return obj->library_name.c_str();
    case kVpiCell:
      if (obj->type != kVpiModule) return nullptr;
      return obj->cell_name.empty() ? obj->name.data() : obj->cell_name.c_str();
    case kVpiConfig:
      if (obj->type != kVpiModule) return nullptr;
      return obj->config_name.c_str();
    default:
      return nullptr;
  }
}

int VpiContext::FreeObject(VpiHandle ) { return 0; }

int VpiContext::Control(int operation, int arg0, int arg1, int arg2,
                        VpiHandle scope) {
  // §38.4: vpiFinish/vpiStop request the matching built-in task on return of the
  // application routine and carry its diagnostic message level (see 20.2).
  if (operation == kVpiFinish) {
    finish_requested_ = true;
    finish_diag_level_ = arg0;
    return 1;
  }
  if (operation == kVpiStop) {
    stop_requested_ = true;
    stop_diag_level_ = arg0;
    return 1;
  }
  // §38.4: vpiReset requests $reset and is passed three additional integer
  // arguments (stop_value, reset_value, diagnostics_value), the same values the
  // $reset task takes (see D.8). Record them, then route through the one
  // DispatchReset path so the reset-callback sequence (§38.36.3) runs exactly as
  // it does for a directly invoked $reset.
  if (operation == kVpiReset) {
    reset_requested_ = true;
    reset_stop_value_ = arg0;
    reset_reset_value_ = arg1;
    reset_diag_value_ = arg2;
    DispatchReset();
    return 1;
  }
  // §38.4: vpiSetInteractiveScope immediately retargets the tool's interactive
  // scope to the supplied vpiScope handle.
  if (operation == kVpiSetInteractiveScope) {
    interactive_scope_ = scope;
    return 1;
  }
  return 0;
}

bool VpiContext::ChkError(VpiErrorInfo* info) {
  if (!info) return last_error_.level != 0;
  *info = last_error_;
  return last_error_.level != 0;
}

void VpiContext::GetVlogInfo(VpiVlogInfo* info) {
  if (!info) return;
  info->argc = 0;
  info->argv = nullptr;
  info->product = product_.c_str();
  info->version = version_.c_str();
}

VpiHandle VpiContext::HandleMulti(int type, VpiHandle ref1, VpiHandle ref2) {
  if (!ref1 && !ref2) return nullptr;

  // §38.22: a request for an intermodule path names the output-port and
  // input-port reference objects the path runs between. Those two ports shall
  // be of the same size; they may, however, sit at different levels of the
  // hierarchy, which is deliberately left unconstrained. A size mismatch cannot
  // describe a valid intermodule path, so report it (§38.2) and return no
  // handle.
  if (type == vpiInterModPath && ref1 && ref2 && ref1->size != ref2->size) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_handle_multi(): the two ports of an intermodule path must be of "
        "the same size";
    return nullptr;
  }

  auto* result = AllocObject();
  result->type = type;
  if (ref1) {
    for (auto* child : ref1->children) {
      if (child->type == type) result->children.push_back(child);
    }
  }
  if (ref2) {
    for (auto* child : ref2->children) {
      if (child->type == type) result->children.push_back(child);
    }
  }
  if (result->children.empty()) return nullptr;
  return result;
}

// §38.3: resolve a handle to the representative of the underlying simulation
// object it denotes by following the same_object_as chain. A bounded walk
// guards against an accidental cycle; the chains the simulator builds are short
// (a handle aliases at most one representative).
static VpiObject* ResolveSameObject(VpiObject* obj) {
  for (int steps = 0; obj && obj->same_object_as && steps < 1000; ++steps) {
    obj = obj->same_object_as;
  }
  return obj;
}

int VpiContext::CompareObjects(VpiHandle obj1, VpiHandle obj2) {
  // §38.3: a null handle names no object, so it can never refer to the same
  // object as anything.
  if (obj1 == nullptr || obj2 == nullptr) return 0;

  VpiObject* a = ResolveSameObject(obj1);
  VpiObject* b = ResolveSameObject(obj2);

  // §38.3: the comparison holds only "provided that the simulation object
  // exists". A handle whose underlying object is absent (e.g. a class handle
  // that is still null) is never equal to anything, even to itself.
  if (!a->object_exists || !b->object_exists) return 0;

  // §38.3: TRUE when both handles resolve to the same underlying object. The
  // representatives are compared, not the original handle pointers, so two
  // distinct handles that alias one object still compare equal - object
  // equivalence cannot be settled by a C "==" of the handles.
  return a == b ? 1 : 0;
}

VpiHandle VpiContext::CreateHandleFor(VpiHandle object) {
  // §37.2.1: a null object denotes nothing, so there is no handle to create.
  if (object == nullptr) return nullptr;

  // Resolve through any existing alias chain to the representative of the
  // underlying object so the new handle points straight at it. The fresh handle
  // is a distinct object (a different pointer than the one passed in), which is
  // the "may create two distinct handles" latitude the standard grants.
  VpiObject* rep = ResolveSameObject(object);
  auto* handle = AllocObject();
  handle->type = rep->type;

  // §37.2.1: the new handle and the original both refer to the same object, so
  // they are equivalent. Recording that this handle denotes `rep` lets
  // vpi_compare_objects() resolve the two to a common representative and report
  // them equal despite their pointers differing.
  handle->same_object_as = rep;
  return handle;
}

void VpiContext::ReleaseHandle(VpiHandle handle) {
  // §37.2.2: vpi_release_handle() causes the tool to release a handle. Marking
  // the handle released is all that is needed: the underlying object is not
  // touched, so a distinct handle to the same object - held perhaps by another
  // VPI program - is unaffected and can still refer to that object. A null
  // handle names nothing.
  if (!handle) return;
  handle->released = true;
}

bool VpiContext::HandleReleased(VpiHandle handle) const {
  return handle != nullptr && handle->released;
}

bool VpiContext::HandleValid(VpiHandle handle) const {
  // §37.2.4: validity runs from a handle's creation until one of the events
  // that ends it. A null handle names no object and so is never valid. A
  // released handle (§37.2.2) is no longer a live handle to its object, and a
  // handle whose object has ceased to exist (§38.3) no longer refers to a live
  // object; both are invalid. Tool termination, the remaining terminating
  // event, disposes of the context and every handle with it, so a handle that
  // is still queryable here has not hit that case. What is left is a valid
  // handle: non-null, unreleased, and naming an object that still exists.
  if (!handle) return false;
  if (handle->released) return false;
  if (!handle->object_exists) return false;
  return true;
}

bool VpiContext::HandleSurvivesRestart(VpiHandle handle) const {
  // §37.2.2 (restart): a restart releases every handle except those naming a
  // cbStartOfRestart or cbEndOfRestart callback. A surviving handle is therefore
  // a callback handle whose registered reason is one of the two restart reasons.
  if (!handle || handle->type != kVpiCallback) return false;
  if (handle->index < 0 ||
      handle->index >= static_cast<int>(callbacks_.size())) {
    return false;
  }
  int reason = callbacks_[handle->index].reason;
  return reason == kCbStartOfRestart || reason == kCbEndOfRestart;
}

void VpiContext::ReleaseHandlesForRestart() {
  // §37.2.2 (restart): release all handles except the restart-callback handles.
  // Every allocated handle is visited; the two surviving kinds are left live.
  for (VpiObject* handle : all_objects_) {
    if (!HandleSurvivesRestart(handle)) handle->released = true;
  }
}

// §37.2.2: release a handle along with the handles to every callback placed on
// the object it names. A callback handle records, in `index`, the slot of the
// callback whose `obj` is the watched object; any such handle is released too.
void VpiContext::ReleaseHandleWithCallbacks(VpiObject* object) {
  if (!object) return;
  object->released = true;
  for (VpiObject* cb : cb_handles_) {
    if (cb->index >= 0 && cb->index < static_cast<int>(callbacks_.size()) &&
        callbacks_[cb->index].obj == object) {
      cb->released = true;
    }
  }
}

// §37.2.2: release a handle, every subelement reachable through its children,
// and the callbacks placed on any of them. Shared by the frame/thread-free and
// class-reclaim rules; the two differ only in which children they descend into.
void VpiContext::ReleaseHandleSubtree(VpiObject* root) {
  if (!root) return;
  ReleaseHandleWithCallbacks(root);
  for (VpiObject* child : root->children) ReleaseHandleSubtree(child);
}

void VpiContext::ReleaseFrameOrThreadObject(VpiHandle root) {
  // §37.2.2 (frame/thread free): release the freed object, all of its
  // subelements, and the callbacks placed on any of them.
  ReleaseHandleSubtree(root);
}

void VpiContext::ReleaseClassObject(VpiHandle class_object) {
  // §37.2.2 (class reclaim): release the class object and the callbacks on it,
  // then release each automatic data member together with all of its
  // subelements. Non-automatic (static) data members are left live - they are
  // not reclaimed with the class object.
  if (!class_object) return;
  ReleaseHandleWithCallbacks(class_object);
  for (VpiObject* member : class_object->children) {
    if (member->automatic) ReleaseHandleSubtree(member);
  }
}

bool VpiContext::SetDefaultCompatibilityMode(int mode) {
  // §36.12.2.2: only one default mode is selectable for a given simulation run.
  // Once a mode has been selected, refuse any request that would change it so
  // the run keeps a single, consistent default; a request for the mode already
  // in force is consistent and is accepted.
  if (default_compat_mode_selected_ && mode != default_compat_mode_) {
    return false;
  }
  default_compat_mode_ = mode;
  default_compat_mode_selected_ = true;
  return true;
}

int VpiContext::EffectiveCompatibilityMode(bool uses_mechanism1,
                                           int mechanism1_mode) const {
  // §36.12.2.2: the run-wide default determines the compatibility-mode VPI
  // behavior for every application not using the compile-based scheme. An
  // application that does use Mechanism 1 is governed by the mode compiled into
  // it, so the default does not apply to it.
  if (uses_mechanism1) {
    return mechanism1_mode;
  }
  return default_compat_mode_;
}

VpiHandle VpiContext::CreateModule(std::string_view name,
                                   std::string full_name) {
  auto* obj = AllocObject();
  obj->type = kVpiModule;
  obj->name = name;
  obj->full_name = std::move(full_name);
  object_map_[name] = obj;
  return obj;
}

VpiHandle VpiContext::CreatePort(std::string_view name, int direction,
                                 VpiHandle parent) {
  auto* obj = AllocObject();
  obj->type = kVpiPort;
  obj->name = name;
  obj->direction = direction;
  obj->parent = parent;
  if (parent) {
    obj->index = static_cast<int>(parent->children.size());
    parent->children.push_back(obj);
  }
  object_map_[name] = obj;
  return obj;
}

VpiHandle VpiContext::CreateParameter(std::string_view name, int int_value) {
  auto* obj = AllocObject();
  obj->type = kVpiParameter;
  obj->name = name;
  obj->size = int_value;
  object_map_[name] = obj;
  return obj;
}

VpiHandle VpiContext::CreateAssertion(std::string_view name, int type) {
  // §37.49: an assertion is registered under one of the assertion-class kinds so
  // a null-referenced iteration over the assertion class (the circle relation)
  // can reach it. An unnamed assertion is not entered in the by-name map.
  auto* obj = AllocObject();
  obj->type = type;
  obj->name = name;
  if (!name.empty()) object_map_[name] = obj;
  return obj;
}

VpiHandle VpiContext::CreateNetObj(std::string_view name, Net* net_ptr,
                                   int width) {
  auto* obj = AllocObject();
  obj->type = kVpiNet;
  obj->name = name;
  obj->net = net_ptr;
  obj->size = width;
  if (net_ptr && net_ptr->resolved) obj->var = net_ptr->resolved;
  object_map_[name] = obj;
  return obj;
}

VpiHandle VpiContext::CreateRegArray(
    std::string_view name, int array_type,
    const std::vector<std::vector<int>>& dim_indices,
    const std::vector<Variable*>& elements) {
  auto* obj = AllocObject();
  obj->type = vpiRegArray;
  obj->name = name;
  obj->array_type = array_type;
  obj->array_dim_indices = dim_indices;
  obj->size = static_cast<int>(elements.size());
  for (size_t i = 0; i < elements.size(); ++i) {
    // §38.35: each element is reachable as a vpiReg over its variable, keyed by
    // its flat ordinal so vpi_put_value_array() can locate it.
    auto* child = AllocObject();
    child->type = kVpiReg;
    child->var = elements[i];
    child->parent = obj;
    child->index = static_cast<int>(i);
    if (elements[i]) child->size = static_cast<int>(elements[i]->value.width);
    obj->children.push_back(child);
  }
  if (!name.empty()) object_map_[name] = obj;
  return obj;
}

Region RegionForPliCallback(int reason) {
  switch (reason) {
    case kCbAfterDelay:
    case kCbNextSimTime:
    case kCbAtStartOfSimTime:
      return Region::kPreActive;

    case kCbReadWriteSynch:
    case kCbNBASynch:
      return Region::kPreNBA;
    case kCbAtEndOfSimTime:
      return Region::kPrePostponed;
    case kCbReadOnlySynch:
      return Region::kPostponed;
    default:
      return Region::kCOUNT;
  }
}

bool IsOneShotPliCallback(int reason) {
  return RegionForPliCallback(reason) != Region::kCOUNT;
}

static VpiContext* g_vpi_context = nullptr;
static VpiContext g_default_context;

VpiContext& GetGlobalVpiContext() {
  if (g_vpi_context) return *g_vpi_context;
  return g_default_context;
}

void SetGlobalVpiContext(VpiContext* ctx) { g_vpi_context = ctx; }

void InvokeVlogStartupRoutines(VlogStartupRoutine* routines) {
  if (!routines) return;
  // §36.10.2: the routines in the vlog_startup_routines[] array execute in the
  // startup phase, when very little VPI functionality is available. Establish
  // that phase for the duration of the walk so the function-availability
  // restriction is in force while the routines register their system
  // tasks/functions and callbacks, then restore the prior phase afterwards. The
  // array-walking itself is unchanged (that is §36.9.1's mechanism); this only
  // narrows the available functionality for its duration.
  VpiContext& ctx = GetGlobalVpiContext();
  VpiToolPhase prior = ctx.ToolPhase();
  ctx.SetToolPhase(VpiToolPhase::kStartup);
  for (size_t i = 0; routines[i] != nullptr; ++i) {
    routines[i]();
  }
  ctx.SetToolPhase(prior);
}

bool VpiPhaseRestrictsFunctionality(VpiToolPhase phase) {
  // §36.10.2: only the full phase (cbEndOfCompile onward) makes all
  // functionality available; the startup phase and the sizetf phase that
  // follows it - which permits no access beyond the startup phase - both
  // restrict it.
  return phase != VpiToolPhase::kFull;
}

bool VpiRoutineAvailableInStartup(VpiRoutine routine) {
  // §36.10.2: only the two registration routines may be called while the
  // vlog_startup_routines[] array executes.
  return routine == VpiRoutine::kRegisterSystf ||
         routine == VpiRoutine::kRegisterCb;
}

bool VpiStartupCallbackReasonAllowed(int reason) {
  // §36.10.2: the only reasons vpi_register_cb() may be registered for while
  // VPI functionality is restricted.
  switch (reason) {
    case kCbEndOfCompile:
    case kCbStartOfSimulation:
    case kCbEndOfSimulation:
    case kCbUnresolvedSystf:
    case kCbError:
    case kCbPLIError:
      return true;
    default:
      return false;
  }
}

bool VpiIsSimulationTimeCallbackReason(int reason) {
  // §38.36.2: the seven time-related callback reasons. Their placement is
  // constrained through the s_cb_data time structure (see RegisterCb).
  switch (reason) {
    case kCbAtStartOfSimTime:
    case kCbNBASynch:
    case kCbReadWriteSynch:
    case kCbAtEndOfSimTime:
    case kCbReadOnlySynch:
    case kCbNextSimTime:
    case kCbAfterDelay:
      return true;
    default:
      return false;
  }
}

bool VpiSystfNameIsValid(const char* tfname) {
  // §38.37.1: the name shall begin with a dollar sign and shall be followed by
  // one or more characters legal in a SystemVerilog simple identifier. A null
  // pointer, an empty string, or a bare "$" with nothing after it fails the
  // "one or more" requirement.
  if (tfname == nullptr || tfname[0] != '$' || tfname[1] == '\0') return false;
  for (const char* p = tfname + 1; *p != '\0'; ++p) {
    char c = *p;
    bool legal = (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ||
                 (c >= '0' && c <= '9') || c == '_' || c == '$';
    if (!legal) return false;
  }
  return true;
}

int VpiSystfReturnType(const VpiSystfData& data) {
  // §38.37.1: sysfunctype shall only be used when type is set to vpiSysFunc, so
  // it names a return-value kind only for a system function; a system task has
  // no return-value kind.
  if (data.type != kVpiSysFunc) return 0;
  return data.sysfunctype;
}

bool VpiSystfCallbackFiresAtBuild(VpiSystfCallback callback) {
  // §38.37.1: callbacks to compiletf and sizetf occur when the simulation data
  // structure is compiled or built; callbacks to calltf occur each time the
  // system task or function is invoked during simulation execution.
  return callback == VpiSystfCallback::kCompiletf ||
         callback == VpiSystfCallback::kSizetf;
}

int VpiSystfInvoke(int (*routine)(const char*), void* user_data) {
  // §38.37.1: the only argument passed to a compiletf/sizetf/calltf routine is
  // the user_data field, typed as PLI_BYTE8 * (char *). One or more of the
  // routine fields may be null when not needed, so a null pointer is skipped.
  if (routine == nullptr) return 0;
  return routine(static_cast<const char*>(user_data));
}

bool VpiSystfSizetfIsCalled(const VpiSystfData& data) {
  // §38.37.1: the sizetf application shall only be called if the type is
  // vpiSysFunc and the sysfunctype is vpiSizedFunc or vpiSizedSignedFunc.
  return data.type == kVpiSysFunc &&
         (data.sysfunctype == kVpiSizedFunc ||
          data.sysfunctype == kVpiSizedSignedFunc);
}

int VpiSystfResultSizeBits(const VpiSystfData& data) {
  // §38.37.1: a sized system function takes its width from the sizetf
  // application when one is provided; with no sizetf it returns 32 bits.
  if (VpiSystfSizetfIsCalled(data) && data.sizetf != nullptr) {
    return VpiSystfInvoke(data.sizetf, data.user_data);
  }
  return kVpiDefaultSizedFuncBits;
}

}

vpiHandle vpi_register_systf(s_vpi_systf_data* data) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().RegisterSystf(data);
}

void vpi_get_systf_info(vpiHandle obj, s_vpi_systf_data* systf_data_p) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  delta::GetGlobalVpiContext().GetSystfInfo(obj, systf_data_p);
}

void vpi_get_cb_info(vpiHandle obj, s_cb_data* cb_data_p) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  delta::GetGlobalVpiContext().GetCbInfo(obj, cb_data_p);
}

void vpi_get_time(vpiHandle obj, s_vpi_time* time_p) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  delta::GetGlobalVpiContext().GetTime(obj, time_p);
}

void vpi_get_delays(vpiHandle obj, p_vpi_delay delay_p) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  delta::GetGlobalVpiContext().GetDelays(obj, delay_p);
}

void vpi_put_delays(vpiHandle obj, p_vpi_delay delay_p) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  delta::GetGlobalVpiContext().PutDelays(obj, delay_p);
}

PLI_INT32 vpi_get_data(PLI_INT32 id, PLI_BYTE8* dataLoc, PLI_INT32 numOfBytes) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().GetData(id, dataLoc, numOfBytes);
}

PLI_INT32 vpi_put_data(PLI_INT32 id, PLI_BYTE8* dataLoc, PLI_INT32 numOfBytes) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().PutData(id, dataLoc, numOfBytes);
}

vpiHandle VpiHandleC(int type, vpiHandle ref) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().Handle(type, ref);
}

vpiHandle vpi_handle_by_name(const char* name, vpiHandle scope) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().HandleByName(name, scope);
}

vpiHandle VpiHandleByIndexC(vpiHandle parent, int index) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().HandleByIndex(index, parent);
}

vpiHandle VpiHandleByMultiIndexC(vpiHandle parent, int num_index,
                                 int* index_array) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().HandleByMultiIndex(num_index, index_array,
                                                         parent);
}

vpiHandle VpiHandleMultiC(int type, vpiHandle ref1, vpiHandle ref2) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().HandleMulti(type, ref1, ref2);
}

int VpiCompareObjectsC(vpiHandle obj1, vpiHandle obj2) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().CompareObjects(obj1, obj2);
}

vpiHandle vpi_iterate(int type, vpiHandle ref) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().Iterate(type, ref);
}

vpiHandle vpi_scan(vpiHandle iterator) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().Scan(iterator);
}

void vpi_get_value(vpiHandle obj, s_vpi_value* value) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  delta::GetGlobalVpiContext().GetValue(obj, value);
}

vpiHandle vpi_put_value(vpiHandle obj, s_vpi_value* value, s_vpi_time* time,
                        int flags) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().PutValue(obj, value, time, flags);
}

void vpi_put_value_array(vpiHandle obj, p_vpi_arrayvalue arrayvalue_p,
                         PLI_INT32* index_p, PLI_UINT32 num) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  delta::GetGlobalVpiContext().PutValueArray(obj, arrayvalue_p, index_p, num);
}

vpiHandle vpi_register_cb(s_cb_data* data) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().RegisterCb(data);
}

int VpiRemoveCbC(vpiHandle cb_handle) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().RemoveCb(cb_handle);
}

int vpi_get(int property, vpiHandle obj) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().Get(property, obj);
}

const char* vpi_get_str(int property, vpiHandle obj) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().GetStr(property, obj);
}

int vpi_free_object(vpiHandle obj) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().FreeObject(obj);
}

int VpiControlC(int operation, ...) {
  // §38.4: vpi_control(operation, varargs) takes a variable number of
  // operation-specific arguments. Read exactly the arguments the operation
  // defines before forwarding the request to the simulator.
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  va_list args;
  va_start(args, operation);
  int result = 0;
  switch (operation) {
    case delta::kVpiStop:
    case delta::kVpiFinish: {
      int diag_level = va_arg(args, int);
      result = delta::GetGlobalVpiContext().Control(operation, diag_level);
      break;
    }
    case delta::kVpiReset: {
      int stop_value = va_arg(args, int);
      int reset_value = va_arg(args, int);
      int diag_value = va_arg(args, int);
      result = delta::GetGlobalVpiContext().Control(operation, stop_value,
                                                    reset_value, diag_value);
      break;
    }
    case delta::kVpiSetInteractiveScope: {
      vpiHandle scope = va_arg(args, vpiHandle);
      result = delta::GetGlobalVpiContext().Control(operation, 0, 0, 0, scope);
      break;
    }
    default:
      result = delta::GetGlobalVpiContext().Control(operation);
      break;
  }
  va_end(args);
  return result;
}

int VpiChkErrorC(SVpiErrorInfo* info) {
  // §38.2: vpi_chk_error() returns the severity level (a Table 38-1 constant) of
  // the error left by the previous VPI routine call, or 0 (false) when that call
  // did not result in an error. When info is non-null the error detail is copied
  // out. Unlike every other VPI routine, vpi_chk_error() does not reset the error
  // status, so the level it reports survives a repeated query.
  auto& ctx = delta::GetGlobalVpiContext();
  ctx.ChkError(info);
  return ctx.LastError().level;
}

void vpi_get_vlog_info(SVpiVlogInfo* info) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  delta::GetGlobalVpiContext().GetVlogInfo(info);
}

namespace delta {

int VpiContext::Flush() {
  // §38.5: flush the buffered output of both the simulator's output channel and
  // the current log file. Committing each buffer into its committed stream and
  // clearing it is the observable effect of forcing the buffered text out. If
  // the underlying flush cannot complete, report failure and leave the buffers
  // intact so nothing is lost.
  if (flush_should_fail_) return 1;
  output_channel_flushed_.append(output_channel_buffer_);
  output_channel_buffer_.clear();
  log_file_flushed_.append(log_file_buffer_);
  log_file_buffer_.clear();
  return 0;
}

}  // namespace delta

PLI_INT32 vpi_flush() {
  // §38.5: vpi_flush() flushes the output buffers for the simulator's output
  // channel and current log file. Like the other VPI entry points it clears the
  // pending error status (§38.2) before doing its work. Returns 0 on success
  // and nonzero on failure.
  delta::GetGlobalVpiContext().ResetErrorStatus();
  return delta::GetGlobalVpiContext().Flush();
}
