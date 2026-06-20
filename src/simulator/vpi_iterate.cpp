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

// Classify a (type, ref) iteration into its special modes. The detailed §37.x
// reasoning for each mode lives at the assignment below; collecting them here
// keeps VpiContext::Iterate focused on dispatch.
VpiIterateModes ComputeVpiIterateModes(int type, VpiHandle ref) {
  VpiIterateModes m;

  // §37.42: a tf call's arguments are reached through vpiArgument. The
  // arguments are the call's argument-kind children (an expr, interface expr,
  // scope, primitive, or named event(-array)), not children whose own type is
  // vpiArgument, so this iteration is recognized specially below.
  m.tf_argument = ref && VpiIsTfCallType(ref->type) && type == vpiArgument;

  // §37.27 detail 1: vpiWaitingProcesses on a named event reaches the threads
  // of every process - static or dynamic - currently waiting on that event. The
  // relation is named for the processes but the objects it reaches are threads,
  // so it is recognized specially rather than matched against the relation
  // name.
  m.named_event_waiting =
      ref && ref->type == vpiNamedEvent && type == vpiWaitingProcesses;

  // §37.27 detail 2: vpiIndex on a named event reaches the index expressions
  // that locate it within an array, starting with the index for the named event
  // and working outward. A named event that is not an array element has no such
  // indices, so the iteration finds none and reports NULL. The relation reaches
  // exprs, not children whose own type is vpiIndex, so it too is special.
  m.named_event_index = ref && ref->type == vpiNamedEvent && type == vpiIndex;

  // §37.18 detail 3: vpiElement on a packed array variable reaches its
  // subelements - struct var, union var, enum var, or (for a multidimensioned
  // packed array) another packed array var - one dimension level at a time. The
  // relation reaches those variable kinds, not children whose own type is
  // literally vpiElement, so it is recognized specially below.
  m.packed_array_var_element =
      ref && ref->type == vpiPackedArrayVar && type == vpiElement;

  // §37.18 detail 6: vpiIndex on a packed array variable reaches the index
  // expressions that locate a subelement within its vpiParent, beginning with
  // the subelement's own index and working outward (the right-to-left textual
  // order). Like the named-event case it reaches exprs, not children whose own
  // type is vpiIndex.
  m.packed_array_var_index =
      ref && ref->type == vpiPackedArrayVar && type == vpiIndex;

  // §37.24 detail 2: vpiElement on an interconnect array reaches its
  // subelements one dimension level at a time - each is itself an interconnect
  // array (a further dimension) or a leaf interconnect net - rather than
  // children whose own type is literally vpiElement.
  m.interconnect_array_element =
      ref && ref->type == vpiInterconnectArray && type == vpiElement;

  // §37.24 detail 1: vpiElement on an interconnect net reaches the net's array
  // elements, but only when the typespec it connects to has a packed or
  // unpacked array data type; a net connected to a non-array type has no such
  // elements.
  m.interconnect_net_element =
      ref && ref->type == vpiInterconnectNet && type == vpiElement &&
      VpiIsInterconnectArrayDataTypespec(VpiInterconnectNetTypespecType(ref));

  // §37.24 detail 1: vpiMember on an interconnect net reaches the net's struct
  // members, but only when the typespec it connects to has a packed or unpacked
  // struct (or union) data type.
  m.interconnect_net_member =
      ref && ref->type == vpiInterconnectNet && type == vpiMember &&
      VpiIsInterconnectStructDataTypespec(VpiInterconnectNetTypespecType(ref));

  // §37.20 detail 1: vpiMemoryWord is a backwards-compatibility relation. A
  // memory has been generalized to a reg array (vpiRegArray) and its words to
  // reg objects (vpiReg). Iterating vpiMemoryWord over a reg array therefore
  // reaches its reg word objects - children whose own kind is vpiReg, not
  // children typed literally vpiMemoryWord - so the relation is recognized
  // specially. The variable and variable-array definitions these objects reuse
  // belong to §37.17.
  m.memory_word = ref && VpiIsArrayVarType(ref->type) && type == vpiMemoryWord;

  // §37.46 (figure): vpiDriver on a net reaches the net's driver objects - a
  // port, a force, a delay terminal, a continuous assignment (whole or single
  // bit), or a primitive terminal - and vpiLoad reaches its load objects. The
  // net case differs from the variable case below: an assignment statement
  // loads but does not drive a net, and a port loads a net only through the
  // complex-expression rule (detail 1), so the net relations are collected by
  // net-specific machinery rather than reused from §37.21.
  m.net_driver = ref && (ref->type == vpiNet || ref->type == vpiNetBit) &&
                 type == vpiDriver;
  m.net_load =
      ref && (ref->type == vpiNet || ref->type == vpiNetBit) && type == vpiLoad;

  // §37.21 (figure): vpiDriver on a variable reaches the variable's driver
  // objects - a port, a force, a continuous assignment (whole or single bit),
  // or a procedural assignment statement - rather than children whose own type
  // is literally vpiDriver. Likewise vpiLoad reaches the variable's load
  // objects. A net reference is handled by §37.46 above, not here.
  m.variable_driver = ref && type == vpiDriver && !m.net_driver;
  m.variable_load = ref && type == vpiLoad && !m.net_load;

  // §37.5 detail 1: the top-level modules are accessed by iterating vpiModule
  // with a NULL reference object. Only top-level modules answer that iteration;
  // a module nested inside another scope is also a vpiModule object but is
  // reached through its parent's internal scope, so it is excluded here.
  m.top_module = !ref && type == kVpiModule;

  // §37.31 detail 1 and §37.33 detail 6: vpiMethods on a class defn or a class
  // object reaches its methods, which are task and function objects (the "task
  // func" node) rather than children whose own type is literally vpiMethods, so
  // this iteration is matched specially and filtered to drop implicit built-in
  // methods (those carrying no explicit declaration) below.
  m.class_methods = ref &&
                    (ref->type == vpiClassDefn || ref->type == vpiClassObj) &&
                    type == vpiMethods;

  // §37.33 detail 3: vpiWaitingProcesses on a class object - a mailbox or a
  // semaphore - reaches the threads of the processes waiting on it, like the
  // named-event case (§37.27). The relation reaches thread objects, not
  // children whose own type is literally vpiWaitingProcesses, so it is matched
  // specially.
  m.class_obj_waiting =
      ref && ref->type == vpiClassObj && type == vpiWaitingProcesses;

  // §37.33 detail 4: vpiMessages on a class object - a mailbox - reaches the
  // messages it holds, which are expression objects rather than children whose
  // own type is literally vpiMessages, so it too is matched specially.
  m.class_obj_messages = ref && ref->type == vpiClassObj && type == vpiMessages;

  // §37.31 detail 3: vpiConstraint on a class defn reaches the class's
  // constraint children directly (a generic type match), but the iteration must
  // return only normal constraints, so inline constraints are dropped below.
  m.class_constraint =
      ref && ref->type == vpiClassDefn && type == vpiConstraint;

  // §37.31 detail 5: vpiDerivedClasses on a class defn reaches the class defns
  // derived from it - again class-defn objects, not children whose own type is
  // vpiDerivedClasses - so the relation is recognized specially.
  m.class_derived =
      ref && ref->type == vpiClassDefn && type == vpiDerivedClasses;

  // §37.31 detail 6: the vpiArgument iteration from an extends object yields
  // the expressions used for constructor chaining (8.17). The arguments are
  // expression children, not children whose own type is vpiArgument, so this is
  // matched specially like a tf call's argument iteration.
  m.extends_argument = ref && ref->type == vpiExtends && type == vpiArgument;

  // §37.12 detail 7: a scope's vpiVirtualInterfaceVar iteration reaches the
  // virtual interface vars it declares (§37.29). When the scope declares an
  // array of virtual interfaces, the iteration yields each element of the array
  // separately, so the array var child is expanded rather than returned whole.
  m.vif = ref && type == vpiVirtualInterfaceVar;

  // §37.12 detail 7: a scope's vpiVariables iteration reports an array of
  // virtual interfaces as the single array var that declares it (not its
  // elements), alongside the scope's ordinary variables.
  m.variables = ref && type == vpiVariables;

  // §37.12 detail 4: a scope's vpiImport iteration reaches the objects actually
  // imported into it through import declarations - the items genuinely
  // referenced across the import (marked imported), rather than children whose
  // own type is literally vpiImport or items merely made visible by the import.
  m.import = ref && type == vpiImport;

  // §37.40 detail 2: a timing check's vpiExpr iteration reaches its arguments.
  // The reference, controlled-reference, and data events are returned as tchk
  // term objects (vpiTchkTerm); every other argument keeps the type of its
  // expression. The relation therefore reaches those terms and expressions, not
  // children whose own type is literally vpiExpr, so it is matched specially.
  m.tchk_expr = ref && ref->type == vpiTchk && type == vpiExpr;

  // §37.38 detail 2: vpiLoopVars on a foreach constraint walks the constraint's
  // index variables in left-to-right order. The objects reached are the index
  // variables (and null-op placeholders for skipped positions), not children
  // whose own type is literally vpiLoopVars, so the iteration is built from the
  // constraint's dedicated loop-var list rather than matched by type.
  m.constr_foreach_loopvars =
      ref && ref->type == vpiConstrForEach && type == vpiLoopVars;

  // §37.75 detail 2: vpiLoopVars on a foreach statement walks the loop's index
  // variables in left-to-right order. As with the foreach constraint above, the
  // objects reached are the index variables (and null-op placeholders for
  // skipped positions), not children whose own type is literally vpiLoopVars,
  // so the iteration is built from the statement's dedicated loop-var list
  // rather than matched by type.
  m.foreach_stmt_loopvars =
      ref && ref->type == vpiForeachStmt && type == vpiLoopVars;

  // §37.38 detail 3: vpiConstraintExpr on a constraint-expression container -
  // an implication, constraint if, constraint if-else, or foreach constraint -
  // walks the body expressions it holds in source order. They are reached from
  // a dedicated body list, not matched as children whose own type is
  // vpiConstraintExpr, so this iteration is recognized specially.
  m.constraint_expr = ref && type == vpiConstraintExpr &&
                      VpiIsConstraintExprContainerType(ref->type);

  // §37.80 (figure): the callback objects placed on a prim term, an expr, a
  // time queue, or a stmt are reached from that object by iterating vpiCallback
  // with the object as the reference. A callback is matched by the object it
  // was registered on (its s_cb_data obj field), since the callback object is
  // not a child of that object. (A NULL reference instead reaches the callbacks
  // not related to such an object - detail 2 - handled by the general walk
  // below, where a callback whose obj field is null answers the null
  // reference.)
  m.callback_object = ref && type == vpiCallback;

  return m;
}

// §37.49 + per-detail rules: decide whether an object of kind obj_type is
// reached by the (type, ref) iteration described by modes. This is the matcher
// the generic child/object walk consults; each special mode that reaches
// objects whose own type is not the relation type is handled before the default
// exact-type comparison.
bool VpiIterateMatches(int obj_type, int type, VpiHandle ref,
                       const VpiIterateModes& modes) {
  // §37.20 detail 1: a reg array's vpiMemoryWord iteration collects its
  // reg word objects (vpiReg), the backwards-compatible form of the
  // legacy memory words, rather than children whose own type is literally
  // vpiMemoryWord.
  if (modes.memory_word) return obj_type == kVpiReg;
  if (type == vpiAssertion) return VpiIsAssertionType(obj_type);
  // §37.31 detail 1 / §37.33 detail 6: a class defn's or class object's
  // vpiMethods iteration collects its method objects - the tasks and
  // functions declared as class items - rather than children whose own
  // type is literally vpiMethods.
  if (modes.class_methods) return VpiIsClassMethodType(obj_type);
  // §37.31 detail 5: a class defn's vpiDerivedClasses iteration collects
  // the class defns derived from it.
  if (modes.class_derived) return obj_type == vpiClassDefn;
  // §37.31 detail 6: an extends object's vpiArgument iteration collects
  // the expressions supplied for constructor chaining.
  if (modes.extends_argument) return VpiIsExprType(obj_type);
  // §37.27 detail 1: a named event's vpiWaitingProcesses iteration
  // collects the thread objects of the waiting processes, not children
  // typed vpiWaitingProcesses.
  if (modes.named_event_waiting) return obj_type == vpiThread;
  // §37.33 detail 3: a class object's vpiWaitingProcesses iteration
  // likewise collects the thread objects of the processes waiting on it.
  if (modes.class_obj_waiting) return obj_type == vpiThread;
  // §37.33 detail 4: a class object's vpiMessages iteration collects the
  // message objects it holds - expressions - not children typed
  // vpiMessages.
  if (modes.class_obj_messages) return VpiIsExprType(obj_type);
  // §37.27 detail 2: a named event's vpiIndex iteration collects the
  // index expressions locating it within its array.
  if (modes.named_event_index) return VpiIsExprType(obj_type);
  // §37.18 detail 3: a packed array variable's vpiElement iteration
  // collects its subelement variables (struct/union/enum/packed-array
  // vars), not children whose own type is vpiElement.
  if (modes.packed_array_var_element) {
    return VpiIsPackedArrayVarElementType(obj_type);
  }
  // §37.18 detail 6: a packed array variable's vpiIndex iteration
  // collects the index expressions locating a subelement within its
  // parent.
  if (modes.packed_array_var_index) return VpiIsExprType(obj_type);
  // §37.24 details 1 and 2: an interconnect array's vpiElement, an
  // interconnect net's vpiElement, and an interconnect net's vpiMember
  // each collect the interconnect subobjects they reach - a nested
  // interconnect array or a leaf interconnect net - not children whose
  // own type is literally vpiElement or vpiMember.
  if (modes.interconnect_array_element || modes.interconnect_net_element ||
      modes.interconnect_net_member) {
    return VpiIsInterconnectSubelementType(obj_type);
  }
  // §37.40 detail 2: a timing check's vpiExpr iteration collects its
  // argument objects - the reference/controlled-reference and data event
  // terms (each a vpiTchkTerm) together with the check's other argument
  // expressions - rather than children whose own type is literally
  // vpiExpr.
  if (modes.tchk_expr) {
    return obj_type == vpiTchkTerm || VpiIsExprType(obj_type);
  }
  // §37.72 detail 1: a case item's match expressions are reached through
  // the vpiExpr edge, which spans both patterns and plain expressions, so
  // the iteration collects every condition the item groups - not only
  // children whose own type happens to be vpiExpr.
  if (ref && ref->type == vpiCaseItem && type == vpiExpr) {
    return VpiIsCaseItemConditionType(obj_type);
  }
  // §37.42: a tf call's vpiArgument iteration collects its argument
  // objects - the exprs, interface exprs, scope, primitive, and
  // named-event(-array) the relation reaches - rather than children whose
  // own type is vpiArgument.
  if (modes.tf_argument) return VpiIsTfCallArgumentType(obj_type);
  // §37.34 detail 5: a constraint's vpiConstraintItem iteration collects
  // every constraint item it groups - the constraint orderings and
  // constraint expressions - in the order they occur, rather than
  // children whose own type is literally vpiConstraintItem.
  if (type == vpiConstraintItem) return VpiIsConstraintItemType(obj_type);
  return obj_type == type;
}

// §37.12 detail 7: collect the scope's virtual interface vars
// (vpiVirtualInterfaceVar) into the iterator, expanding a declared array of
// virtual interfaces into its individual elements. The iteration is supported
// only in an elaborated context; within a lexical context such as a class defn
// (§37.31) it is not supported and yields nothing.
void CollectVirtualInterfaceVars(VpiObject* ref, VpiObject* iter) {
  if (ref->type == vpiClassDefn) return;
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
void DispatchVpiIterate(int type, VpiHandle ref, const VpiIterateModes& modes,
                        std::vector<VpiObject*>& all_objects,
                        const std::vector<VpiTimeQueueSlot>& time_queue_slots,
                        const std::vector<VpiHandle>& cb_handles,
                        const std::vector<VpiCbData>& callbacks,
                        VpiObject* iter) {
  if (modes.vif) {
    CollectVirtualInterfaceVars(ref, iter);
  } else if (modes.variables) {
    CollectScopeVariables(ref, iter);
  } else if (modes.import) {
    CollectImportedObjects(ref, iter);
  } else if (!ref && type == vpiUserSystf) {
    CollectUserSystf(all_objects, iter);
  } else if (!ref && type == vpiTimeQueue) {
    CollectTimeQueueSlots(time_queue_slots, all_objects, iter);
  } else if (modes.net_driver || modes.net_load) {
    CollectNetDriversOrLoads(ref, modes.net_driver, iter);
  } else if (modes.variable_driver || modes.variable_load) {
    CollectVariableDriversOrLoads(ref, modes.variable_driver,
                                  VpiIsStructUnionOrClassVar(ref->type), iter);
  } else if (modes.constr_foreach_loopvars || modes.foreach_stmt_loopvars) {
    CollectForeachLoopVars(ref, all_objects, iter);
  } else if (modes.constraint_expr) {
    CollectConstraintExprs(ref, iter);
  } else if (modes.callback_object) {
    CollectCallbackObjects(ref, cb_handles, callbacks, iter);
  } else if (ref) {
    CollectMatchingChildren(type, ref, modes, iter);
  } else {
    CollectMatchingObjects(type, ref, modes, all_objects, iter);
  }
}

}  // namespace

VpiHandle VpiContext::Iterate(int type, VpiHandle ref) {
  // Classify this (type, ref) iteration into its special modes. The detailed
  // §37.x reasoning for each mode lives in ComputeVpiIterateModes; collecting
  // them there keeps this routine focused on dispatch.
  const VpiIterateModes modes = ComputeVpiIterateModes(type, ref);

  // §38.23: unless otherwise specified, iterating the relationships of a
  // protected object is an error, so no iterator is produced. §37.42 detail 10
  // carves out one exception: a protected system task or function call shall
  // still allow iteration over its vpiArgument relation. Every other protected
  // iteration is still refused.
  if (ref && ref->is_protected && !modes.tf_argument) return nullptr;

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
  DispatchVpiIterate(type, ref, modes, all_objects_, time_queue_slots_,
                     cb_handles_, callbacks_, iter);

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
