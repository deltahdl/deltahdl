#include "simulator/vpi.h"

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

}  // namespace

void VpiContext::GetDelays(VpiHandle obj, VpiDelay* delay_p) {
  // §38.10 / §38.1: the structure and its da array are application-allocated.
  // With nothing to fill, or no object to read delays from, there is nothing
  // to do; the routine never allocates anything itself.
  if (delay_p == nullptr || obj == nullptr) return;

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
      for (auto* child : within->children) {
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
      return true;
    default:
      return false;
  }
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

  // §38.23: vpi_handle(vpiUse, iterator) recovers the reference object the
  // iterator was created to walk.
  if (type == vpiUse && ref->type == vpiIterator) return ref->iter_ref;

  // §37.11 detail 1: traversing vpiExpr from an instance array reaches the
  // operation object that lists the array's actual connections, not a child
  // whose own type happens to be vpiExpr.
  if (type == vpiExpr && VpiIsInstanceArrayType(ref->type)) {
    return VpiInstanceArrayConnections(ref);
  }

  if (ref->parent && ref->parent->type == type) return ref->parent;

  for (auto* child : ref->children) {
    if (child->type == type) return child;
  }
  return nullptr;
}

VpiHandle VpiContext::Iterate(int type, VpiHandle ref) {
  // §38.23: unless otherwise specified, iterating the relationships of a
  // protected object is an error, so no iterator is produced.
  if (ref && ref->is_protected) return nullptr;

  // §38.23: the handle returned is an iterator whose own type is vpiIterator;
  // the requested object type only selects which related objects it walks. The
  // reference object is remembered so it can be recovered through vpiUse.
  auto* iter = new VpiObject();
  iter->type = vpiIterator;
  iter->iter_ref = ref;
  iter->scan_index = 0;

  // §37.49: vpiAssertion names the assertion class rather than a single object
  // kind, so iterating it collects every object the class groups (the circle
  // relation, when ref is null) instead of matching one exact type.
  auto matches = [type](int obj_type) {
    if (type == vpiAssertion) return VpiIsAssertionType(obj_type);
    return obj_type == type;
  };

  if (ref) {
    for (auto* child : ref->children) {
      if (matches(child->type)) iter->children.push_back(child);
    }
  } else {
    for (auto* obj : all_objects_) {
      if (matches(obj->type)) iter->children.push_back(obj);
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

void VpiContext::GetValue(VpiHandle obj, VpiValue* value) {
  if (!obj || !value || !obj->var) return;
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

  callbacks_.push_back(*data);

  auto* cb_obj = AllocObject();
  cb_obj->type = kVpiCallback;
  cb_obj->index = static_cast<int>(callbacks_.size() - 1);
  cb_handles_.push_back(cb_obj);
  return cb_obj;
}

int VpiContext::RemoveCb(VpiHandle cb_handle) {
  if (!cb_handle) return 0;
  if (cb_handle->type != kVpiCallback) return 0;
  int idx = cb_handle->index;
  if (idx >= 0 && idx < static_cast<int>(callbacks_.size())) {
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
    data.cb_rtn(&data);
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
  switch (property) {
    case kVpiType:
      return obj->type;
    // §37.3.6: every object carries a vpiIsProtected Boolean property (not drawn
    // in the data model diagrams) reporting whether the handle denotes protected
    // code; TRUE when protected, FALSE otherwise.
    case vpiIsProtected:
      return obj->is_protected ? 1 : 0;
    case kVpiSize:
      return obj->size;
    case kVpiDirection:
      return obj->direction;
    // §37.3.7: declared lifetime as a Boolean (0 static, 1 non-static).
    case kVpiAutomatic:
      return obj->automatic ? 1 : 0;
    // §37.3.7: the object's allocation scheme; defaults to kVpiOtherScheme.
    case kVpiAllocScheme:
      return obj->alloc_scheme;
    // §37.54 (D2): an operation reports its operation type as an int property.
    case vpiOpType:
      return obj->op_type;
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
      return obj->name.data();
    // §37.49: the file component of an assertion's source location. The general
    // vpiFile semantics (and the `line directive's effect) are §37.3.3/§22.12's;
    // here the stored file string is handed back, or null when unset.
    case vpiFile:
      return obj->file.empty() ? nullptr : obj->file.c_str();
    case kVpiFullName:
      return obj->full_name.empty() ? obj->name.data() : obj->full_name.c_str();
    case kVpiDefName:
      if (obj->type == kVpiModule) return obj->name.data();
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

void vpi_get_time(vpiHandle obj, s_vpi_time* time_p) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  delta::GetGlobalVpiContext().GetTime(obj, time_p);
}

void vpi_get_delays(vpiHandle obj, p_vpi_delay delay_p) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  delta::GetGlobalVpiContext().GetDelays(obj, delay_p);
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
