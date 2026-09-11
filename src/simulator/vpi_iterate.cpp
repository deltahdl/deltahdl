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

#include "simulator/vpi.h"
// §37.10 detail 3: the package/interface/program instance kinds are defined in
// the SystemVerilog VPI header alongside the §37.10 vpiInstance relation.
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"

namespace delta {

// ===========================================================================
// §37.46 Net drivers and loads.
// ===========================================================================

bool VpiIsPortsType(int type) {
  // §37.46 (figure): the `ports` enclosure inside both the net drivers and the
  // net loads classes is dotted, so §37.4.1 makes it a class - a grouping of
  // "other objects and classes" that is never an object itself. §37.14 draws a
  // port and a port bit inside it, and §37.4.1 has a relation drawn to a class
  // reach the kinds the class groups, so both are what the two edges mean by a
  // port.
  return type == vpiPort || type == vpiPortBit;
}

bool VpiIsNetDriverType(int type) {
  // §37.46 (figure, net drivers): a port, a force, a delay terminal, a
  // continuous assignment (whole or single bit), or a primitive terminal.
  // Unlike a variable (§37.21) a net is not driven by a procedural assignment
  // statement.
  //
  // The ports enclosure was read as the single kind vpiPort, so a port bit
  // driving a net was a driver to nothing.
  if (VpiIsPortsType(type)) return true;
  switch (type) {
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
  if (!port || !VpiIsPortsType(port->type)) return false;
  if (port->direction != vpiInput) return false;
  VpiObject* expr = port->high_conn;
  if (!expr || expr->type != vpiOperation) return false;
  return !VpiIsConcatenationExpression(expr);
}

namespace {

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
    } else if (VpiIsPortsType(child->type)) {
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
  // §37.19: a var select's vpiIndex relation, which reaches the index
  // expressions that select into its vpiParent array.
  bool var_select_index = false;
  bool interconnect_array_element = false;
  bool interconnect_net_element = false;
  bool interconnect_net_member = false;
  bool memory_word = false;
  // §36.12 Table 36-10 item 6: a vpiReg iteration over an array variable.
  bool array_var_elements = false;
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
  // §37.38 (figure): a constraint if-else's vpiElseConst relation.
  bool else_constraint_expr = false;
  bool callback_object = false;
  // §37.57 detail 1: a let expression's vpiArgument iteration, which reads the
  // let declaration's formals rather than the expression's own children.
  bool let_argument = false;
  // §37.39: one of a module path's three path-term relations.
  bool mod_path_terms = false;
  // §37.26: a structure or union's vpiMember relation.
  bool struct_union_members = false;
  // §36.10.3: an operation's vpiOperand relation.
  bool operation_operands = false;
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
  // §37.57 (figure): a let expression carries a vpiArgument edge of its own,
  // and detail 1 gives it a rule the tf call's edge does not have.
  m.let_argument = ref && ref->type == vpiLetExpr && type == vpiArgument;
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
  // §37.19 (figure): the var select's vpiIndex arrows reach expr, the same
  // shape one dimension level up. Nothing recognized the relation, so the index
  // expressions a select was written with were reachable from it by nothing.
  // §37.58 (figure) draws the same vpiIndex edge from a bit select to expr.
  m.var_select_index = ref && type == vpiIndex &&
                       (ref->type == vpiVarSelect || ref->type == vpiBitSelect);
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
  // §36.12 Table 36-10 item 6: in the IEEE 1800 standards a vpiReg iteration on
  // a vpiRegArray retrieves array elements of other variable kinds too, the
  // array object being what §37.17 represents an unpacked array of any variable
  // with.
  m.array_var_elements = ref && VpiIsArrayVarType(ref->type) && type == kVpiReg;
  // §37.45 (figure): a delay terminal's vpiDriver and vpiLoad are drawn to the
  // `net drivers` and `net loads` classes of §37.46, not to §37.21's variable
  // ones. A delay terminal was named by neither line, so both relations fell to
  // the variable arm below and gathered the kinds that drive a variable - which
  // a delay terminal connects to none of.
  const bool kDelayTerm = ref && ref->type == vpiDelayTerm;
  m.net_driver =
      ref && (ref->type == vpiNet || ref->type == vpiNetBit || kDelayTerm) &&
      type == vpiDriver;
  m.net_load = ref &&
               (ref->type == vpiNet || ref->type == vpiNetBit || kDelayTerm) &&
               type == vpiLoad;
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
  // §37.38 (figure): a constraint if-else's else branch, drawn as a relation of
  // its own and recognized by nothing, so it was reachable from the if-else by
  // nothing either.
  m.else_constraint_expr =
      ref && type == vpiElseConst && ref->type == vpiConstrIfElse;
  m.callback_object = ref && type == vpiCallback;
  // §36.10.3: an operation reaches its operands, which carry their own
  // expression kinds rather than the relation tag.
  m.operation_operands = ref && type == vpiOperand && ref->type == vpiOperation;
  // §37.26: a structure or union reaches the members it holds through
  // vpiMember, whose targets carry their own variable or net kind.
  m.struct_union_members =
      ref && type == vpiMember && VpiIsStructOrUnionType(ref->type);
  // §37.39: a module path's three path-term relations, which reach terms whose
  // own type is vpiPathTerm rather than the relation tag.
  m.mod_path_terms = ref && ref->type == vpiModPath &&
                     (type == vpiModPathIn || type == vpiModPathOut ||
                      type == vpiModDataPathIn);
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
  if (modes.array_var_elements) {
    *matched = VpiIsVariablesType(obj_type);
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
  if (modes.packed_array_var_index || modes.var_select_index) {
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
  // §37.35/§37.5: the module-to-primitive edge is drawn to the `primitive`
  // class, so it reaches the gates, switches and UDPs the class groups.
  // Matching the class constant against an object's own type reached none of
  // them: §37.4.1 makes the enclosure a grouping and no object is one.
  if (type == vpiPrimitive) return VpiIsPrimitiveType(obj_type);
  // §37.9/§37.5/§37.63: the edge from a program or a module to its procedures
  // is drawn to the `process` class, so it reaches the initial, final and
  // always procedures the class groups rather than an object whose own type is
  // the class name, which is a kind no procedure has.
  if (type == vpiProcess) return VpiIsProcessType(obj_type);
  // §37.20 detail 1: vpiMemory is a method returning vpiRegArray objects.
  if (type == vpiMemory) return obj_type == VpiMemoryIterationItemType();
  // §37.11/§37.5: the module's edges to `instance array` and to the `primitive
  // array` nested inside it are drawn to those class enclosures, so they reach
  // the module, interface, program, gate, switch and udp arrays the two group.
  if (type == vpiInstanceArray) return VpiIsInstanceArrayType(obj_type);
  if (type == vpiPrimitiveArray) return VpiIsPrimitiveArrayType(obj_type);
  // §37.24/§37.40/§37.72/§37.42/§37.34: the edge-specific special modes.
  if (VpiIterateMatchesEdgeMode(obj_type, type, ref, modes, &matched)) {
    return matched;
  }
  return obj_type == type;
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

// §37.44 (the circle relation): the run's threads, reached by an iteration with
// a null reference. Every thread object the context has made is one of the
// run's, VpiContext::RefreshThreadObjects having made them from the processes
// the run switched to and the branches those spawned, so the objects themselves
// are the list -- a fork branch is a thread of the run as much as the always
// procedure that forked it is.
void CollectThreads(const std::vector<VpiObject*>& all_objects,
                    VpiObject* iter) {
  for (auto* obj : all_objects) {
    if (obj->type == vpiThread) iter->children.push_back(obj);
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
    // §37.2.3: "Handle equivalence cannot be determined with a C '==='
    // comparison. The function vpi_compare_objects() compares the objects they
    // refer to." A callback is placed on an object, not on the handle the
    // application happened to register it through, so a second handle to that
    // object has to find it - and pointer equality found it only through the
    // one handle.
    if (GetGlobalVpiContext().CompareObjects(callbacks[idx].obj, ref) != 0) {
      iter->children.push_back(cb_obj);
    }
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

// §37.4.3: a relationship traversed with NULL for the ref_h is one the data
// model diagrams draw from a circle. Every other relationship is drawn from a
// reference object and means nothing without one, which §38.23 says in its own
// terms: the iterator walks "all objects of type type associated with object
// ref". These are the one-to-many relationships this model draws from a circle
// and answers by sweeping the objects it holds - §37.5 detail 1's top-level
// modules ("Top-level modules shall be accessed using vpi_iterate() with a NULL
// reference object"), §37.80's registered callbacks and §39.3.1's assertions.
// §37.42's user-defined system tf objects, §37.81's time queue and §37.44's
// threads are drawn from a circle too and are answered ahead of this out of
// their own registries.
bool VpiIsNullReferenceRelation(int type) {
  // §37.36 (figure) draws the udp defn from a circle too: a UDP definition
  // belongs to no scope, so the application reaches the design's definitions
  // with a NULL reference object. The relation was not among these, so an
  // iteration over them was a walk of the reference object's children and a
  // NULL reference reached nothing.
  return type == kVpiModule || type == vpiCallback || type == vpiAssertion ||
         type == vpiUdpDefn;
}

// §37.57 detail 1: whether the instantiation left this argument position empty.
// §37.42 detail 8 is how the model writes an omitted call argument - an
// operation whose vpiOpType is the null operation - and a let instantiation
// that writes nothing for a port leaves the same hole.
bool VpiLetArgumentIsOmitted(VpiHandle actual) {
  return actual != nullptr && actual->type == vpiOperation &&
         actual->op_type == vpiNullOp;
}

// §37.57 (figure) + detail 1: collect a let expression's arguments. The formals
// are the seq formal decls of the let declaration the expression's tagless edge
// reaches, in declaration order, and the actuals are the expressions the
// instantiation wrote. Detail 1 puts the arguments in formal order and fills an
// omitted one from its formal's default value, "so that the correspondence
// between each argument and its respective formal can be made".
//
// Nothing collected these. vpiArgument is a relation tag and no object's type
// is one, so the generic child walk this fell through to matched nothing, a let
// expression's arguments were reachable by no route, and VpiLetExprArguments --
// the rule detail 1 states - was called by no routine in the simulator.
void CollectLetExprArguments(VpiObject* ref, VpiObject* iter) {
  VpiHandle decl = nullptr;
  std::vector<VpiHandle> provided;
  for (auto* child : ref->children) {
    if (child->type == vpiLetDecl) {
      decl = child;
    } else if (VpiIsExprType(child->type)) {
      provided.push_back(VpiLetArgumentIsOmitted(child) ? nullptr : child);
    }
  }

  std::vector<VpiLetFormal> formals;
  for (VpiHandle formal : VpiSeqFormals(decl)) {
    formals.push_back(VpiLetFormal{VpiLetFormalDefault(formal)});
  }

  for (VpiHandle argument : VpiLetExprArguments(formals, provided)) {
    // A formal the instantiation left empty and that declares no default has
    // no argument object to hand back. §11.12 requires a value for such a
    // formal, so no let a compilation accepted reaches this.
    if (argument != nullptr) iter->children.push_back(argument);
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
    for (VpiHandle vif : VpiScopeVirtualInterfaceVars(ref)) {
      iter->children.push_back(vif);
    }
    return true;
  }
  if (modes.variables) {
    for (VpiHandle var : VpiScopeVariables(ref)) {
      iter->children.push_back(var);
    }
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
  if (!ref && type == vpiThread) {
    CollectThreads(all_objects, iter);
    return true;
  }
  return false;
}

// §37.46/§37.21/§37.38/§37.75/§37.80: route the reference-object special modes
// computed from a non-null reference - net/variable drivers and loads, foreach
// loop variables, constraint-expression bodies, and registered callback
// objects. Returns true if one of these modes applied.
// §36.10.3/§37.26/§37.39: route the reference-object modes whose collector
// hands back the objects as a list - an operation's operands, the members of a
// structure or union, and the terms of a module path. They are grouped apart
// from the modes above so neither dispatcher grows past the complexity limit
// clang-tidy-src holds every function under.
bool DispatchListedMode(int type, VpiHandle ref, const VpiIterateModes& modes,
                        VpiObject* iter) {
  std::vector<VpiHandle> listed;
  if (modes.operation_operands) {
    listed = VpiOperationOperands(ref);
  } else if (modes.struct_union_members) {
    listed = VpiStructUnionMembers(ref);
  } else if (modes.mod_path_terms) {
    listed = VpiModPathTerms(type, ref);
  } else {
    return false;
  }
  for (VpiHandle object : listed) iter->children.push_back(object);
  return true;
}

bool DispatchRefSpecialMode(int type, VpiHandle ref,
                            const VpiIterateModes& modes,
                            VpiIterateStores& stores, VpiObject* iter) {
  if (modes.net_driver || modes.net_load) {
    CollectNetDriversOrLoads(ref, modes.net_driver, iter);
    return true;
  }
  if (modes.variable_driver || modes.variable_load) {
    // §37.21 detail 1 descends through a structure, union or class variable;
    // detail 2 says the same of a variable array, whose drivers and loads
    // "should include driver/load for entire array/vector or any portion of an
    // array/vector to which a handle can be obtained". Only the aggregate arm
    // was applied, so an array's elements and the selects into them were walked
    // by nothing and the relation reported the whole array's drivers alone.
    const bool kDescend = VpiIsStructUnionOrClassVar(ref->type) ||
                          VpiIsVariableArrayType(ref->type);
    CollectVariableDriversOrLoads(ref, modes.variable_driver, kDescend, iter);
    return true;
  }
  if (modes.constr_foreach_loopvars || modes.foreach_stmt_loopvars) {
    CollectForeachLoopVars(ref, stores.all_objects, iter);
    return true;
  }
  if (modes.else_constraint_expr) {
    VpiCollectElseConstraintExprs(ref, iter);
    return true;
  }
  if (modes.constraint_expr) {
    VpiCollectConstraintExprs(ref, iter);
    return true;
  }
  if (DispatchListedMode(type, ref, modes, iter)) return true;
  if (modes.let_argument) {
    CollectLetExprArguments(ref, iter);
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
  } else if (VpiIsNullReferenceRelation(type)) {
    // §37.4.3: the sweep answers only where a circle originates the
    // relationship. Asked for anything else, a null reference names no
    // traversal, and the empty iterator the caller then discards is the NULL
    // §38.23 gives an iteration with no objects.
    CollectMatchingObjects(type, ref, modes, stores.all_objects, iter);
  }
}

}  // namespace

VpiHandle VpiContext::Iterate(int type, VpiHandle ref, int compatibility_mode) {
  // §37.44: a thread that started since the last iteration is one of the run's
  // threads too, so the objects are brought up to date before this one answers.
  RefreshThreadObjects();

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
  // §36.12.3: "If the design contains unsupported constructs, the behavior of
  // the VPI implementation is undefined. The extent of checking for consistency
  // between constructs and mode is left to the discretion of the VPI
  // implementation." This is the extent of it: an application running under a
  // compatibility mode that reaches a construct its standard has no notion of
  // is told so through §38.2's error, rather than left with a behavior nobody
  // defined. What it reached still comes back, because §36.12.2 rules out
  // emulating a construct that has no older behavior to emulate.
  const char* unsupported =
      VpiCompatibilityUnsupportedConstruct(compatibility_mode, iter->children);
  if (unsupported != nullptr) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = unsupported;
  }
  return iter;
}

VpiHandle VpiContext::Scan(VpiHandle iterator) {
  // §38.40: walk the objects an iterator (from vpi_iterate()) was built over,
  // handing back the next one on each call so the traversal advances one object
  // at a time. A null handle has nothing to traverse.
  if (!iterator) return nullptr;
  // §38.40 Arguments: the one handle this routine takes is a "handle to an
  // iterator object returned from vpi_iterate()", and §38.23 makes that handle
  // an object of type vpiIterator. Any other object directs no traversal, so
  // walking its children hands an application objects out of a call the clause
  // gives no meaning to -- and retiring it at the end of that walk destroys an
  // object the context owns and goes on owning. It is refused instead, with the
  // §38.2 error an application reads through vpi_chk_error().
  if (iterator->type != vpiIterator) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_scan(): the handle is not an iterator returned from vpi_iterate()";
    return nullptr;
  }
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
