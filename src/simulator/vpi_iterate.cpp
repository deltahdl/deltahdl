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
#include "simulator/vpi_internal.h"

namespace delta {

bool VpiIsVariableDriverType(int type) {
  // §37.21 (figure, variable drivers): the kinds that drive a variable - a
  // port, a force, a continuous assignment, a single bit of a continuous
  // assignment, or a procedural assignment statement.
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
  // lists the driver kinds without a port - an assignment statement, a force,
  // and a continuous assignment or single bit of one - because a port only ever
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
  // continuous assignment (whole or single bit), or a primitive terminal.
  // Unlike a variable (§37.21) a net is not driven by a procedural assignment
  // statement.
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
// drive/load their nets individually, so a concatenation on a port does not
// make the whole port a complex-expression load.
bool VpiIsConcatenationExpression(VpiObject* expr) {
  return expr->type == vpiOperation &&
         (expr->op_type == vpiConcatOp || expr->op_type == vpiMultiConcatOp);
}

}  // namespace

bool VpiPortIsComplexExpressionLoad(VpiHandle port) {
  // §37.46 detail 1: a complex expression on an input port - an operation other
  // than a concatenation - loads the nets it reads, and the port is then the
  // load object reported when iterating the net's loads. A simple reference is
  // a direct connection rather than a complex-expression load, a
  // concatenation's operands connect their nets individually, and only an input
  // port loads this way. The complex expression itself is reached through
  // vpiHighConn (§37.14).
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

// §37.21 detail 1: the children worth descending into when gathering the
// drivers or loads of an aggregate variable - a bit-select or part-select of
// the variable, or a member nested inside it (itself any variable kind,
// including a further aggregate that is walked recursively).
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

// §37.21 (figure) + detail 1: gather a variable's drivers (want_driver) or
// loads into the iterator. The variable's own driver/load children are always
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

// §37.46 (figure) + detail 1: gather a net's drivers (want_driver) or loads
// into the iterator. A driver/load is one of the object-kind children the
// figure lists. On the driver side a port is always a driver; on the load side
// a port is reported only when it carries a complex, non-concatenation
// expression on an input (detail 1).
void CollectNetDriversOrLoads(VpiObject* node, bool want_driver,
                              VpiObject* iter) {
  for (auto* child : node->children) {
    if (want_driver) {
      if (VpiIsNetDriverType(child->type)) iter->children.push_back(child);
    } else if (child->type == vpiPort) {
      if (VpiPortIsComplexExpressionLoad(child))
        iter->children.push_back(child);
    } else if (VpiIsNetLoadType(child->type)) {
      iter->children.push_back(child);
    }
  }
}

// The set of "special" iteration modes recognized for a given (type, ref) pair.
// Many VPI relations reach objects whose own type is not literally the relation
// type (§37.x details cited at each field's computation), so each is flagged
// once here and consulted by the matcher and the dispatch below. Bundling the
// flags keeps the per-relation reasoning in one place and lets the matcher run
// as a plain free function rather than a large capture-heavy lambda.
struct VpiIterateModes {
  bool tf_argument = false;
  bool named_event_waiting = false;
  bool named_event_index = false;
  bool packed_array_var_element = false;
  bool packed_array_var_index = false;
  bool interconnect_array_element = false;
  bool interconnect_net_element = false;
  bool interconnect_net_member = false;
  bool memory_word = false;
  bool net_driver = false;
  bool net_load = false;
  bool variable_driver = false;
  bool variable_load = false;
  bool top_module = false;
  bool class_methods = false;
  bool class_obj_waiting = false;
  bool class_obj_messages = false;
  bool class_constraint = false;
  bool class_derived = false;
  bool extends_argument = false;
  bool vif = false;
  bool variables = false;
  bool import = false;
  bool tchk_expr = false;
  bool constr_foreach_loopvars = false;
  bool foreach_stmt_loopvars = false;
  bool constraint_expr = false;
  bool callback_object = false;
};

// The context-owned object and registry stores an iteration is resolved
// against. §37.42 detail 6 / §37.81 reach the simulator's full object list and
// surviving time-queue slots (both grown as placeholder/time-queue objects are
// allocated, so held by non-const reference like VpiContext::AllocObject's
// bookkeeping); §37.80 (figure) reaches the read-only callback registry. These
// four collections always travel together from VpiContext::Iterate through the
// dispatch helpers, so they are bundled as one entity rather than threaded
// through each signature individually.
struct VpiIterateStores {
  std::vector<VpiObject*>& all_objects;
  const std::vector<VpiTimeQueueSlot>& time_queue_slots;
  const std::vector<VpiHandle>& cb_handles;
  const std::vector<VpiCbData>& callbacks;
};

// §37.42 / §37.27: classify the tf-call argument and named-event special
// modes. A tf call's arguments are reached through vpiArgument (argument-kind
// children, not vpiArgument-typed children); a named event's
// vpiWaitingProcesses reaches the waiting threads and its vpiIndex reaches the
// locating index expressions.
void ComputeTfAndEventModes(int type, VpiHandle ref, VpiIterateModes& m) {
  m.tf_argument = ref && VpiIsTfCallType(ref->type) && type == vpiArgument;
  m.named_event_waiting =
      ref && ref->type == vpiNamedEvent && type == vpiWaitingProcesses;
  m.named_event_index = ref && ref->type == vpiNamedEvent && type == vpiIndex;
}

// §37.18 details 3 and 6: classify the packed-array-variable special modes.
// vpiElement reaches the subelement variables one dimension at a time;
// vpiIndex reaches the index expressions locating a subelement within its
// parent. Both reach objects whose own type is not the relation type.
void ComputePackedArrayModes(int type, VpiHandle ref, VpiIterateModes& m) {
  m.packed_array_var_element =
      ref && ref->type == vpiPackedArrayVar && type == vpiElement;
  m.packed_array_var_index =
      ref && ref->type == vpiPackedArrayVar && type == vpiIndex;
}

// §37.24 details 1 and 2: classify the interconnect special modes. An
// interconnect array's vpiElement reaches its nested arrays/leaf nets; an
// interconnect net's vpiElement and vpiMember reach array elements or struct
// members only when its connected typespec has the matching array/struct data
// type.
void ComputeInterconnectModes(int type, VpiHandle ref, VpiIterateModes& m) {
  m.interconnect_array_element =
      ref && ref->type == vpiInterconnectArray && type == vpiElement;
  m.interconnect_net_element =
      ref && ref->type == vpiInterconnectNet && type == vpiElement &&
      VpiIsInterconnectArrayDataTypespec(VpiInterconnectNetTypespecType(ref));
  m.interconnect_net_member =
      ref && ref->type == vpiInterconnectNet && type == vpiMember &&
      VpiIsInterconnectStructDataTypespec(VpiInterconnectNetTypespecType(ref));
}

// §37.20 detail 1 / §37.46 (figure) / §37.21 (figure): classify the
// memory-word and net/variable driver/load special modes. vpiMemoryWord on a
// reg array reaches its reg word objects; vpiDriver/vpiLoad reach a net's or a
// variable's driver/load objects (the net case differs from the variable case
// per §37.46), rather than children whose own type is the relation type.
void ComputeDriverLoadModes(int type, VpiHandle ref, VpiIterateModes& m) {
  m.memory_word = ref && VpiIsArrayVarType(ref->type) && type == vpiMemoryWord;
  m.net_driver = ref && (ref->type == vpiNet || ref->type == vpiNetBit) &&
                 type == vpiDriver;
  m.net_load =
      ref && (ref->type == vpiNet || ref->type == vpiNetBit) && type == vpiLoad;
  m.variable_driver = ref && type == vpiDriver && !m.net_driver;
  m.variable_load = ref && type == vpiLoad && !m.net_load;
}

// §37.31 details 1/3/5/6 + §37.33 details 3/4/6: classify the class special
// modes. vpiMethods reaches a class's task/function objects;
// vpiWaitingProcesses and vpiMessages on a class object reach waiting threads
// and held message expressions; vpiConstraint and vpiDerivedClasses reach a
// class defn's constraints and derived class defns; and an extends object's
// vpiArgument reaches the constructor-chaining expressions.
void ComputeClassModes(int type, VpiHandle ref, VpiIterateModes& m) {
  m.class_methods = ref &&
                    (ref->type == vpiClassDefn || ref->type == vpiClassObj) &&
                    type == vpiMethods;
  m.class_obj_waiting =
      ref && ref->type == vpiClassObj && type == vpiWaitingProcesses;
  m.class_obj_messages = ref && ref->type == vpiClassObj && type == vpiMessages;
  m.class_constraint =
      ref && ref->type == vpiClassDefn && type == vpiConstraint;
  m.class_derived =
      ref && ref->type == vpiClassDefn && type == vpiDerivedClasses;
  m.extends_argument = ref && ref->type == vpiExtends && type == vpiArgument;
}

// §37.12 details 4/7: classify the scope special modes. A scope's
// vpiVirtualInterfaceVar iteration reaches the virtual interface vars it
// declares (expanding an array into its elements); vpiVariables reports such an
// array whole alongside ordinary variables; vpiImport reaches the objects
// actually imported into the scope.
void ComputeScopeModes(int type, VpiHandle ref, VpiIterateModes& m) {
  m.vif = ref && type == vpiVirtualInterfaceVar;
  m.variables = ref && type == vpiVariables;
  m.import = ref && type == vpiImport;
}

// §37.40 detail 2 / §37.38 details 2/3 / §37.75 detail 2 / §37.80 (figure):
// classify the timing-check, constraint, foreach-loop-var, and callback special
// modes. A timing check's vpiExpr reaches its term/expr arguments; a foreach
// constraint's or statement's vpiLoopVars reaches its index variables; a
// constraint-expression container's vpiConstraintExpr reaches its body
// expressions; and a vpiCallback iteration is matched by the object a callback
// was registered on.
void ComputeConstraintAndCallbackModes(int type, VpiHandle ref,
                                       VpiIterateModes& m) {
  m.tchk_expr = ref && ref->type == vpiTchk && type == vpiExpr;
  m.constr_foreach_loopvars =
      ref && ref->type == vpiConstrForEach && type == vpiLoopVars;
  m.foreach_stmt_loopvars =
      ref && ref->type == vpiForeachStmt && type == vpiLoopVars;
  m.constraint_expr = ref && type == vpiConstraintExpr &&
                      VpiIsConstraintExprContainerType(ref->type);
  m.callback_object = ref && type == vpiCallback;
}

// Classify a (type, ref) iteration into its special modes. The detailed §37.x
// reasoning for each mode lives in the per-group helpers above; collecting them
// here keeps VpiContext::Iterate focused on dispatch. §37.5 detail 1: the
// top-level modules are accessed by iterating vpiModule with a NULL reference;
// a nested module is reached through its parent's internal scope instead.
VpiIterateModes ComputeVpiIterateModes(int type, VpiHandle ref) {
  VpiIterateModes m;
  ComputeTfAndEventModes(type, ref, m);
  ComputePackedArrayModes(type, ref, m);
  ComputeInterconnectModes(type, ref, m);
  ComputeDriverLoadModes(type, ref, m);
  ComputeClassModes(type, ref, m);
  ComputeScopeModes(type, ref, m);
  ComputeConstraintAndCallbackModes(type, ref, m);
  m.top_module = !ref && type == kVpiModule;
  return m;
}

// §37.49 + per-detail rules: decide whether an object of kind obj_type is
// reached by the (type, ref) iteration described by modes. This is the matcher
// the generic child/object walk consults; each special mode that reaches
// objects whose own type is not the relation type is handled before the default
// exact-type comparison.
// §37.20/§37.31/§37.33/§37.18 (selected): resolve the special modes whose
// match reduces to a fixed object kind or a kind predicate - the reg-array
// memory word (vpiReg), the class method/derived/extends-argument relations,
// the named-event/class-object waiting threads, the class-object messages, the
// named-event index, and the packed-array subelement/index relations. Returns
// true if one of these modes applied and writes its verdict into *matched, so
// the caller can preserve the original precedence by consulting these first.
bool VpiIterateMatchesKindMode(int obj_type, const VpiIterateModes& modes,
                               bool* matched) {
  if (modes.memory_word) {
    *matched = obj_type == kVpiReg;
    return true;
  }
  if (modes.class_methods) {
    *matched = VpiIsClassMethodType(obj_type);
    return true;
  }
  if (modes.class_derived) {
    *matched = obj_type == vpiClassDefn;
    return true;
  }
  if (modes.extends_argument) {
    *matched = VpiIsExprType(obj_type);
    return true;
  }
  if (modes.named_event_waiting || modes.class_obj_waiting) {
    *matched = obj_type == vpiThread;
    return true;
  }
  if (modes.class_obj_messages || modes.named_event_index) {
    *matched = VpiIsExprType(obj_type);
    return true;
  }
  if (modes.packed_array_var_element) {
    *matched = VpiIsPackedArrayVarElementType(obj_type);
    return true;
  }
  if (modes.packed_array_var_index) {
    *matched = VpiIsExprType(obj_type);
    return true;
  }
  return false;
}

// §37.24/§37.40/§37.72/§37.42/§37.34 (selected): resolve the remaining special
// modes that reach edge-specific objects - the interconnect subelements, a
// timing check's term/expr arguments, a case item's match conditions, a tf
// call's arguments, and a constraint's constraint items. Returns true if one of
// these applied and writes its verdict into *matched. These are checked after
// the kind-mode group so the original precedence is preserved.
bool VpiIterateMatchesEdgeMode(int obj_type, int type, VpiHandle ref,
                               const VpiIterateModes& modes, bool* matched) {
  if (modes.interconnect_array_element || modes.interconnect_net_element ||
      modes.interconnect_net_member) {
    *matched = VpiIsInterconnectSubelementType(obj_type);
    return true;
  }
  if (modes.tchk_expr) {
    *matched = obj_type == vpiTchkTerm || VpiIsExprType(obj_type);
    return true;
  }
  if (ref && ref->type == vpiCaseItem && type == vpiExpr) {
    *matched = VpiIsCaseItemConditionType(obj_type);
    return true;
  }
  if (modes.tf_argument) {
    *matched = VpiIsTfCallArgumentType(obj_type);
    return true;
  }
  if (type == vpiConstraintItem) {
    *matched = VpiIsConstraintItemType(obj_type);
    return true;
  }
  return false;
}

bool VpiIterateMatches(int obj_type, int type, VpiHandle ref,
                       const VpiIterateModes& modes) {
  bool matched = false;
  // §37.20 detail 1: a reg array's vpiMemoryWord iteration collects reg word
  // objects, etc. - the fixed-kind special modes resolved first to preserve
  // precedence.
  if (VpiIterateMatchesKindMode(obj_type, modes, &matched)) return matched;
  // §37.x: the vpiAssertion relation reaches every assertion kind, checked
  // between the two grouped mode blocks exactly as in the original order.
  if (type == vpiAssertion) return VpiIsAssertionType(obj_type);
  // §37.24/§37.40/§37.72/§37.42/§37.34: the edge-specific special modes.
  if (VpiIterateMatchesEdgeMode(obj_type, type, ref, modes, &matched)) {
    return matched;
  }
  return obj_type == type;
}

// §37.12 detail 7: collect the scope's virtual interface vars
// (vpiVirtualInterfaceVar) into the iterator, expanding a declared array of
// virtual interfaces into its individual elements. The iteration is supported
// only in an elaborated context; within a lexical context such as a class defn
// (§37.31) it is not supported and yields nothing.
// §37.12 detail 7: expand a declared array of virtual interfaces into its
// individual virtual interface var elements, appending each to the iterator.
void CollectVirtualInterfaceArrayElems(VpiObject* array_var, VpiObject* iter) {
  for (auto* elem : array_var->children) {
    if (elem->type == vpiVirtualInterfaceVar) {
      iter->children.push_back(elem);
    }
  }
}

void CollectVirtualInterfaceVars(VpiObject* ref, VpiObject* iter) {
  if (ref->type == vpiClassDefn) return;
  for (auto* child : ref->children) {
    if (child->type == vpiVirtualInterfaceVar) {
      iter->children.push_back(child);
    } else if (VpiIsVirtualInterfaceArray(child)) {
      CollectVirtualInterfaceArrayElems(child, iter);
    }
  }
}

// §37.12 detail 7: collect the scope's variables (vpiVariables), reporting an
// array of virtual interfaces as the single array var that declares it rather
// than expanded.
void CollectScopeVariables(VpiObject* ref, VpiObject* iter) {
  for (auto* child : ref->children) {
    if (child->type == vpiVariables || VpiIsVirtualInterfaceArray(child)) {
      iter->children.push_back(child);
    }
  }
}

// §37.12 detail 4: collect the objects actually imported into the scope - those
// referenced across an import declaration, marked imported.
void CollectImportedObjects(VpiObject* ref, VpiObject* iter) {
  for (auto* child : ref->children) {
    if (child->imported) iter->children.push_back(child);
  }
}

// §37.42 detail 6: collect every registered user-defined system task or
// function object (callbacks marked as a system tf), found by that mark rather
// than by a plain type match.
void CollectUserSystf(const std::vector<VpiObject*>& all_objects,
                      VpiObject* iter) {
  for (auto* obj : all_objects) {
    if (obj->is_systf) iter->children.push_back(obj);
  }
}

// §37.81: collect the surviving simulation-time-queue slots. Detail 3: the slot
// at the current simulation time takes part only when events remain scheduled
// before its read-only synch region; a future slot always contributes. Detail
// 1: the surviving slots are handed back in increasing order of simulation
// time, so they are sorted by time and a time queue object carrying that time
// is produced for each. The new objects are registered in all_objects to match
// VpiContext::AllocObject's bookkeeping.
void CollectTimeQueueSlots(
    const std::vector<VpiTimeQueueSlot>& time_queue_slots,
    std::vector<VpiObject*>& all_objects, VpiObject* iter) {
  std::vector<VpiTimeQueueSlot> slots;
  for (const auto& slot : time_queue_slots) {
    if (slot.is_current && !slot.has_events_before_read_only_synch) continue;
    slots.push_back(slot);
  }
  std::sort(slots.begin(), slots.end(),
            [](const VpiTimeQueueSlot& a, const VpiTimeQueueSlot& b) {
              return a.time < b.time;
            });
  for (const auto& slot : slots) {
    auto* tq = new VpiObject();
    all_objects.push_back(tq);
    tq->type = kVpiTimeQueue;
    tq->time_queue_time = slot.time;
    // §38.13: this object stands for a concrete queue slot, so vpi_get_time()
    // reports its recorded slot time rather than the scheduler's next event.
    tq->has_scheduled_time = true;
    iter->children.push_back(tq);
  }
}

// §37.38 detail 2 / §37.75 detail 2: collect a foreach constraint's or foreach
// statement's index variables in left-to-right order. A skipped index position
// - stored as a null slot in the list - is reported as a freshly built
// vpiOperation whose operator is the null operation, so the caller still sees a
// placeholder occupying that slot. The placeholder objects are registered in
// all_objects to match VpiContext::AllocObject's bookkeeping.
void CollectForeachLoopVars(VpiObject* ref,
                            std::vector<VpiObject*>& all_objects,
                            VpiObject* iter) {
  for (auto* loop_var : ref->loop_vars) {
    if (loop_var) {
      iter->children.push_back(loop_var);
    } else {
      auto* placeholder = new VpiObject();
      all_objects.push_back(placeholder);
      VpiMakeEmptyArgument(placeholder);
      iter->children.push_back(placeholder);
    }
  }
}

// §37.38 detail 3: collect the container's body constraint expressions in the
// order they occur in the implication, if, if-else, or foreach.
void CollectConstraintExprs(VpiObject* ref, VpiObject* iter) {
  for (auto* expr : ref->constraint_exprs) {
    iter->children.push_back(expr);
  }
}

// §37.80 (figure): collect the callback objects registered on the reference
// object - each registered callback whose s_cb_data obj field names it. The
// callback object itself is not a child of the object, so it is found through
// the callback registry rather than the generic child walk.
void CollectCallbackObjects(VpiObject* ref,
                            const std::vector<VpiHandle>& cb_handles,
                            const std::vector<VpiCbData>& callbacks,
                            VpiObject* iter) {
  for (auto* cb_obj : cb_handles) {
    int idx = cb_obj->index;
    if (idx < 0 || idx >= static_cast<int>(callbacks.size())) continue;
    if (callbacks[idx].obj == ref) iter->children.push_back(cb_obj);
  }
}

// §37.49: the generic child walk - collect every child the (type, ref)
// iteration matches. §37.31 detail 1 drops implicit built-in methods from a
// vpiMethods iteration; §37.31 detail 3 drops inline constraints from a
// vpiConstraint iteration.
void CollectMatchingChildren(int type, VpiHandle ref,
                             const VpiIterateModes& modes, VpiObject* iter) {
  for (auto* child : ref->children) {
    if (!VpiIterateMatches(child->type, type, ref, modes)) continue;
    if (modes.class_methods && child->implicit_builtin_method) continue;
    if (modes.class_constraint && child->inline_constraint) continue;
    iter->children.push_back(child);
  }
}

// §37.49 + §37.5 detail 1: the null-reference walk - collect every object the
// (type, ref) iteration matches. A NULL-reference vpiModule iteration reaches
// only the top-level modules, never a module nested within another scope.
void CollectMatchingObjects(int type, VpiHandle ref,
                            const VpiIterateModes& modes,
                            const std::vector<VpiObject*>& all_objects,
                            VpiObject* iter) {
  for (auto* obj : all_objects) {
    if (!VpiIterateMatches(obj->type, type, ref, modes)) continue;
    if (modes.top_module && !obj->top_module) continue;
    iter->children.push_back(obj);
  }
}

// §37.49 + per-detail rules: route the (type, ref) iteration to the collector
// for its special mode, falling through to the generic child walk (a non-null
// reference) or the null-reference walk. The context-owned collections the
// special modes need are passed by reference. Detail 2 of §37.81 - an empty
// time queue yields NULL rather than an empty iterator - is left to the shared
// empty-children check by the caller.
// §37.12 details 4/7: route the scope special modes - virtual interface vars,
// variables, and imports - to their collectors. Returns true if one of these
// modes applied.
bool DispatchScopeMode(int type, VpiHandle ref, const VpiIterateModes& modes,
                       VpiObject* iter) {
  (void)type;
  if (modes.vif) {
    CollectVirtualInterfaceVars(ref, iter);
    return true;
  }
  if (modes.variables) {
    CollectScopeVariables(ref, iter);
    return true;
  }
  if (modes.import) {
    CollectImportedObjects(ref, iter);
    return true;
  }
  return false;
}

// §37.42 detail 6 / §37.81: route the null-reference registry modes - the
// user-defined system tf objects and the surviving simulation-time-queue slots.
// Returns true if one of these modes applied.
bool DispatchRegistryMode(int type, VpiHandle ref,
                          std::vector<VpiObject*>& all_objects,
                          const std::vector<VpiTimeQueueSlot>& time_queue_slots,
                          VpiObject* iter) {
  if (!ref && type == vpiUserSystf) {
    CollectUserSystf(all_objects, iter);
    return true;
  }
  if (!ref && type == vpiTimeQueue) {
    CollectTimeQueueSlots(time_queue_slots, all_objects, iter);
    return true;
  }
  return false;
}

// §37.46/§37.21/§37.38/§37.75/§37.80: route the reference-object special modes
// computed from a non-null reference - net/variable drivers and loads, foreach
// loop variables, constraint-expression bodies, and registered callback
// objects. Returns true if one of these modes applied.
bool DispatchRefSpecialMode(int type, VpiHandle ref,
                            const VpiIterateModes& modes,
                            VpiIterateStores& stores, VpiObject* iter) {
  (void)type;
  if (modes.net_driver || modes.net_load) {
    CollectNetDriversOrLoads(ref, modes.net_driver, iter);
    return true;
  }
  if (modes.variable_driver || modes.variable_load) {
    CollectVariableDriversOrLoads(ref, modes.variable_driver,
                                  VpiIsStructUnionOrClassVar(ref->type), iter);
    return true;
  }
  if (modes.constr_foreach_loopvars || modes.foreach_stmt_loopvars) {
    CollectForeachLoopVars(ref, stores.all_objects, iter);
    return true;
  }
  if (modes.constraint_expr) {
    CollectConstraintExprs(ref, iter);
    return true;
  }
  if (modes.callback_object) {
    CollectCallbackObjects(ref, stores.cb_handles, stores.callbacks, iter);
    return true;
  }
  return false;
}

void DispatchVpiIterate(int type, VpiHandle ref, const VpiIterateModes& modes,
                        VpiIterateStores& stores, VpiObject* iter) {
  if (DispatchScopeMode(type, ref, modes, iter)) return;
  if (DispatchRegistryMode(type, ref, stores.all_objects,
                           stores.time_queue_slots, iter)) {
    return;
  }
  if (DispatchRefSpecialMode(type, ref, modes, stores, iter)) {
    return;
  }
  if (ref) {
    CollectMatchingChildren(type, ref, modes, iter);
  } else {
    CollectMatchingObjects(type, ref, modes, stores.all_objects, iter);
  }
}

}  // namespace

VpiHandle VpiContext::Iterate(int type, VpiHandle ref) {
  // Classify this (type, ref) iteration into its special modes. The detailed
  // §37.x reasoning for each mode lives in ComputeVpiIterateModes; collecting
  // them there keeps this routine focused on dispatch.
  const VpiIterateModes kModes = ComputeVpiIterateModes(type, ref);

  // §38.23: unless otherwise specified, iterating the relationships of a
  // protected object is an error, so no iterator is produced. §37.42 detail 10
  // carves out one exception: a protected system task or function call shall
  // still allow iteration over its vpiArgument relation. Every other protected
  // iteration is still refused.
  if (ref && ref->is_protected && !kModes.tf_argument) return nullptr;

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

  // §37.49 + per-detail rules: route the iteration to the collector for its
  // special mode (or the generic walks). Detail 2 of §37.81 - an empty time
  // queue yields NULL rather than an empty iterator - is left to the shared
  // empty-children check below.
  VpiIterateStores stores{all_objects_, time_queue_slots_, cb_handles_,
                          callbacks_};
  DispatchVpiIterate(type, ref, kModes, stores, iter);

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

}  // namespace delta
