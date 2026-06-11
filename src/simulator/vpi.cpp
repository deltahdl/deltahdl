#include "simulator/vpi.h"

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

VpiHandle VpiContext::HandleByIndex(int index, VpiHandle parent) {
  if (!parent) return nullptr;
  for (auto* child : parent->children) {
    if (child->index == index) return child;
  }
  return nullptr;
}

VpiHandle VpiContext::Handle(int type, VpiHandle ref) {
  if (!ref) return nullptr;

  // §38.23: vpi_handle(vpiUse, iterator) recovers the reference object the
  // iterator was created to walk.
  if (type == vpiUse && ref->type == vpiIterator) return ref->iter_ref;

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

void VpiContext::PutValue(VpiHandle obj, VpiValue* value, VpiTime* ,
                          int ) {
  if (!obj || !value) return;
  if (!obj->var && !obj->net) return;

  if (scheduler_) scheduler_->NoteWriteAttempt();
  if (!obj->var) return;
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
  // §38.6: unless otherwise specified, asking vpi_get() for any property of a
  // protected object is an error. Record the error and return vpiUndefined,
  // the value vpi_get() yields whenever an error occurs.
  if (obj->is_protected) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message = "vpi_get() on a protected object is an error";
    return vpiUndefined;
  }
  switch (property) {
    case kVpiType:
      return obj->type;
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
    // §37.52 detail 3: an operation reports whether it is the strong version of
    // its operator as a Boolean property (TRUE for the strong form).
    case vpiOpStrong:
      return obj->op_strong ? 1 : 0;
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
    case vpiExpanded:
      return obj->is_vectored ? 0 : 1;
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

const char* VpiContext::GetStr(int property, VpiHandle obj) {
  if (!obj) return nullptr;
  switch (property) {
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
  delta::GetGlobalVpiContext().PutValue(obj, value, time, flags);
  return obj;
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
