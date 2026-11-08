#include <algorithm>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_class_objects.h"
#include "simulator/vpi_class_typespecs.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_constraint_relations.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_io_decl_stand_in.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_simple_expr_uses.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

struct VpiIterateModes {
  bool tf_argument = false;
  bool named_event_waiting = false;
  bool named_event_index = false;
  bool packed_array_var_element = false;
  bool packed_array_var_index = false;
  bool var_select_index = false;
  bool interconnect_array_element = false;
  bool interconnect_net_element = false;
  bool interconnect_net_member = false;
  bool memory_word = false;
  bool array_var_elements = false;
  bool net_driver = false;
  bool net_load = false;
  bool net_local = false;
  bool net_relation = false;
  bool net_relation_driver = false;
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
  bool constraint_list = false;
  bool callback_object = false;
  bool let_argument = false;
  bool terms_and_ports = false;
  bool struct_union_members = false;
  bool operation_operands = false;
  bool for_header_stmts = false;
  bool ordered_wait_events = false;
  bool simple_expr_use = false;
  bool net_cont_assign = false;
};

struct VpiIterateStores {
  std::vector<VpiObject*>& all_objects;
  const std::vector<VpiTimeQueueSlot>& time_queue_slots;
  const std::vector<VpiHandle>& cb_handles;
  const std::vector<s_cb_data>& callbacks;
};

void ComputeTfAndEventModes(int type, VpiHandle ref, VpiIterateModes& m) {
  m.tf_argument = ref &&
                  (VpiIsTfCallType(ref->type) || ref->type == vpiPropertyInst ||
                   ref->type == vpiSequenceInst) &&
                  type == vpiArgument;
  m.let_argument = ref && ref->type == vpiLetExpr && type == vpiArgument;
  m.named_event_waiting =
      ref && ref->type == vpiNamedEvent && type == vpiWaitingProcesses;
  m.named_event_index = ref && ref->type == vpiNamedEvent && type == vpiIndex;
  m.ordered_wait_events =
      ref && ref->type == vpiOrderedWait && type == vpiCondition;
}

void ComputePackedArrayModes(int type, VpiHandle ref, VpiIterateModes& m) {
  m.packed_array_var_element = ref && type == vpiElement &&
                               (ref->type == vpiPackedArrayVar ||
                                VpiNetElementIteratorApplies(ref->type));
  m.packed_array_var_index =
      ref && ref->type == vpiPackedArrayVar && type == vpiIndex;
  m.var_select_index =
      ref && type == vpiIndex &&
      (ref->type == vpiVarSelect || ref->type == vpiBitSelect ||
       ref->type == vpiRegBit || ref->type == vpiNetBit ||
       (ref->array_member &&
        (VpiIsVariablesType(ref->type) || VpiIsNetsType(ref->type))));
}

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

void ComputeDriverLoadModes(int type, VpiHandle ref, VpiIterateModes& m) {
  m.memory_word = ref && VpiIsArrayVarType(ref->type) && type == vpiMemoryWord;
  m.array_var_elements = ref && VpiIsArrayVarType(ref->type) && type == kVpiReg;
  const bool kNetSide =
      ref && (VpiIsNetsType(ref->type) || ref->type == vpiDelayTerm);
  m.net_driver = kNetSide && type == vpiDriver;
  m.net_load = kNetSide && type == vpiLoad;
  m.net_local = ref && VpiIsNetsType(ref->type) &&
                (type == vpiLocalDriver || type == vpiLocalLoad);
  m.net_relation = m.net_driver || m.net_load || m.net_local;
  m.net_relation_driver =
      m.net_driver || (m.net_local && type == vpiLocalDriver);
  m.variable_driver = ref && type == vpiDriver && !m.net_driver;
  m.variable_load = ref && type == vpiLoad && !m.net_load;
  m.simple_expr_use = type == vpiUse && VpiIsSimpleExpr(ref);
  m.net_cont_assign = ref && VpiIsNetsType(ref->type) && type == vpiContAssign;
}

void ComputeClassModes(int type, VpiHandle ref, VpiIterateModes& m) {
  m.class_methods = ref &&
                    (ref->type == vpiClassDefn || ref->type == vpiClassObj ||
                     ref->type == vpiClassTypespec) &&
                    type == vpiMethods;
  m.class_obj_waiting =
      ref && ref->type == vpiClassObj && type == vpiWaitingProcesses;
  m.class_obj_messages = ref && ref->type == vpiClassObj && type == vpiMessages;
  m.class_constraint =
      ref && ref->type == vpiClassDefn && type == vpiConstraint;
  m.class_derived = ref && ref->type == vpiClassDefn &&
                    (type == vpiDerivedClasses || type == vpiClassTypespec);
  m.extends_argument = ref && ref->type == vpiExtends && type == vpiArgument;
}

void ComputeScopeModes(int type, VpiHandle ref, VpiIterateModes& m) {
  m.vif = ref && type == vpiVirtualInterfaceVar;
  m.variables = ref && type == vpiVariables;
  m.import = ref && type == vpiImport;
}

void ComputeConstraintAndCallbackModes(int type, VpiHandle ref,
                                       VpiIterateModes& m) {
  m.tchk_expr = ref && ref->type == vpiTchk && type == vpiExpr;
  m.constr_foreach_loopvars =
      ref && ref->type == vpiConstrForEach && type == vpiLoopVars;
  m.foreach_stmt_loopvars =
      ref && ref->type == vpiForeachStmt && type == vpiLoopVars;
  m.constraint_expr = ref && type == vpiConstraintExpr &&
                      VpiIsConstraintExprContainerType(ref->type);
  m.constraint_list = ref && VpiConstraintListOf(type, ref) != nullptr;
  m.callback_object = type == vpiCallback;
  m.for_header_stmts = ref && ref->type == vpiFor &&
                       (type == vpiForInitStmt || type == vpiForIncStmt);
  m.operation_operands = ref && type == vpiOperand && ref->type == vpiOperation;
  m.struct_union_members =
      ref && type == vpiMember && VpiIsStructOrUnionType(ref->type);
  m.terms_and_ports = ref && VpiIsTermOrPortRelation(type, ref);
}

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

bool VpiIterateMatchesKindMode(int obj_type, const VpiIterateModes& modes,
                               bool* matched) {
  if (modes.memory_word) {
    *matched = obj_type == kVpiReg;
    return true;
  }
  if (modes.ordered_wait_events) {
    *matched = !VpiIsScopeBodyStmtType(obj_type);
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
    *matched = VpiIsPackedArrayVarElementType(obj_type) ||
               VpiIsPackedArrayNetElementType(obj_type);
    return true;
  }
  if (modes.packed_array_var_index) {
    *matched = VpiIsExprType(obj_type);
    return true;
  }
  if (modes.var_select_index) {
    *matched = VpiIsExprOperandType(obj_type);
    return true;
  }
  return false;
}

bool VpiIterateMatchesEdgeMode(VpiHandle obj, int type, VpiHandle ref,
                               const VpiIterateModes& modes, bool* matched) {
  if (modes.interconnect_array_element || modes.interconnect_net_element ||
      modes.interconnect_net_member) {
    *matched = VpiIsInterconnectSubelementType(obj->type);
    return true;
  }
  if (ref && ref->type == vpiCaseItem && type == vpiExpr) {
    *matched = VpiIsCaseItemConditionType(obj->type) && !obj->written_as_stmt;
    return true;
  }
  if (type == vpiBit) {
    *matched = VpiIsBitObjectType(obj->type);
    return true;
  }
  if (type == vpiConstraintItem) {
    *matched = VpiIsConstraintItemType(obj->type);
    return true;
  }
  return false;
}

bool VpiIterateMatchesClass(int type, int obj_type, bool& matched) {
  switch (type) {
    case vpiPrimitive:
      matched = VpiIsPrimitiveType(obj_type);
      return true;
    case vpiProcess:
      matched = VpiIsProcessType(obj_type);
      return true;
    case vpiTaskFunc:
      matched = VpiIsTaskFuncType(obj_type);
      return true;
    case vpiNet:
      matched = VpiIsNetClassType(obj_type);
      return true;
    case vpiInstance:
      matched = VpiIsInstanceType(obj_type);
      return true;
    case vpiParameter:
      matched = obj_type == vpiParameter || obj_type == vpiTypeParameter;
      return true;
    default:
      return false;
  }
}

static bool HeldBesideIndices(VpiHandle obj, VpiHandle ref) {
  if (obj->parent != ref) return false;
  return obj->type == vpiRegBit || obj->type == vpiNetBit || obj->array_member;
}

bool VpiIterateMatches(VpiHandle obj, int type, VpiHandle ref,
                       const VpiIterateModes& modes) {
  bool matched = false;
  if (modes.var_select_index && HeldBesideIndices(obj, ref)) return false;
  if (VpiIterateMatchesKindMode(obj->type, modes, &matched)) return matched;
  if (type == vpiAssertion) return VpiIsAssertionType(obj->type);
  if (type == vpiFsmStates) return obj->type == vpiFsmHandle;
  if (VpiIterateMatchesClass(type, obj->type, matched)) return matched;
  if (type == vpiMemory) return obj->type == VpiMemoryIterationItemType();
  if (type == vpiNetTypedef) return obj->type == vpiNettypeDecl;
  if (type == vpiTypedef)
    return VpiIsTypespecType(obj->type) && obj->type != vpiTypeParameter;
  if (type == vpiInstanceArray) return VpiIsInstanceArrayType(obj->type);
  if (type == vpiPrimitiveArray) return VpiIsPrimitiveArrayType(obj->type);
  if (VpiIterateMatchesEdgeMode(obj, type, ref, modes, &matched)) {
    return matched;
  }
  return obj->type == type;
}

void CollectImportedObjects(VpiObject* ref, VpiObject* iter) {
  for (auto* child : ref->children) {
    if (child->imported) iter->children.push_back(child);
  }
  for (VpiObject* item : ref->instance_facts.imported) {
    iter->children.push_back(item);
  }
}

void CollectUserSystf(const std::vector<VpiObject*>& all_objects,
                      VpiObject* iter) {
  for (auto* obj : all_objects) {
    if (obj->is_systf) iter->children.push_back(obj);
  }
}

void CollectThreads(const std::vector<VpiObject*>& all_objects,
                    VpiObject* iter) {
  for (auto* obj : all_objects) {
    if (obj->type == vpiThread) iter->children.push_back(obj);
  }
}

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
    tq->has_scheduled_time = true;
    iter->children.push_back(tq);
  }
}

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

void CollectMatchingChildren(int type, VpiHandle ref,
                             const VpiIterateModes& modes, VpiObject* iter) {
  for (auto* child : ref->children) {
    if (!VpiIterateMatches(child, type, ref, modes)) continue;
    if (modes.class_methods && child->implicit_builtin_method) continue;
    if (modes.class_constraint && child->inline_constraint) continue;
    iter->children.push_back(child);
  }
}

bool VpiIsNullReferenceRelation(int type) {
  return type == kVpiModule || type == vpiAssertion || type == vpiUdpDefn ||
         type == vpiPackage || type == vpiClassDefn;
}

bool VpiLetArgumentIsOmitted(VpiHandle actual) {
  return actual->type == vpiOperation && actual->op_type == vpiNullOp;
}

void CollectLetExprArguments(VpiObject* ref, VpiObject* iter) {
  VpiHandle decl = nullptr;
  std::vector<VpiHandle> provided;
  for (auto* child : ref->children) {
    if (child->type == vpiLetDecl) {
      decl = child;
    } else if (VpiIsExprOperandType(child->type)) {
      provided.push_back(VpiLetArgumentIsOmitted(child) ? nullptr : child);
    }
  }

  std::vector<VpiLetFormal> formals;
  for (VpiHandle formal : VpiSeqFormals(decl)) {
    formals.push_back(VpiLetFormal{VpiLetFormalDefault(formal)});
  }

  for (VpiHandle argument : VpiLetExprArguments(formals, provided)) {
    if (argument != nullptr) iter->children.push_back(argument);
  }
}

void CollectMatchingObjects(int type, VpiHandle ref,
                            const VpiIterateModes& modes,
                            const std::vector<VpiObject*>& all_objects,
                            VpiObject* iter) {
  for (auto* obj : all_objects) {
    if (!VpiIterateMatches(obj, type, ref, modes)) continue;
    if (modes.top_module && !obj->top_module) continue;
    if (type == vpiClassDefn && !obj->in_compilation_unit) continue;
    iter->children.push_back(obj);
  }
}

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

bool DispatchListedMode(int type, VpiHandle ref, const VpiIterateModes& modes,
                        VpiObject* iter) {
  std::vector<VpiHandle> listed;
  if (modes.operation_operands) {
    listed = VpiOperationOperands(ref);
  } else if (modes.struct_union_members) {
    listed = VpiStructUnionMembers(ref);
  } else if (modes.terms_and_ports) {
    listed = VpiTermOrPortObjects(type, ref);
  } else if (modes.simple_expr_use) {
    listed = VpiSimpleExprUses(ref);
  } else if (modes.net_cont_assign) {
    listed = VpiNetContAssigns(ref);
  } else if (modes.tchk_expr) {
    listed = ref->tchk_arguments;
  } else {
    return false;
  }
  for (VpiHandle object : listed) iter->children.push_back(object);
  return true;
}

bool DispatchRefSpecialMode(int type, VpiHandle ref,
                            const VpiIterateModes& modes,
                            VpiIterateStores& stores, VpiObject* iter) {
  if (modes.net_relation) {
    iter->children =
        VpiNetDriversOrLoads(ref, modes.net_relation_driver, modes.net_local);
    return true;
  }
  if (modes.variable_driver || modes.variable_load) {
    const bool kDescend = VpiIsStructUnionOrClassVar(ref->type) ||
                          VpiIsVariableArrayType(ref->type);
    VpiCollectVariableDriversOrLoads(ref, modes.variable_driver, kDescend,
                                     iter);
    return true;
  }
  if (modes.class_derived) {
    iter->children = VpiClassDefnList(type, *ref);
    return true;
  }
  if (modes.constr_foreach_loopvars || modes.foreach_stmt_loopvars) {
    CollectForeachLoopVars(ref, stores.all_objects, iter);
    return true;
  }
  if (modes.constraint_list) {
    iter->children = *VpiConstraintListOf(type, ref);
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
    VpiCollectCallbackObjects(ref, stores.cb_handles, stores.callbacks, iter);
    return true;
  }
  if (modes.for_header_stmts) {
    VpiCollectForHeaderStmts(type, ref, iter);
    return true;
  }
  if (modes.tf_argument) {
    VpiCollectTfCallArguments(ref, iter);
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
    if (VpiCollectNestedObjects(type, ref, iter)) return;
    CollectMatchingChildren(type, ref, modes, iter);
  } else if (VpiIsNullReferenceRelation(type)) {
    CollectMatchingObjects(type, ref, modes, stores.all_objects, iter);
  }
}

}  // namespace

VpiHandle VpiContext::Iterate(int type, VpiHandle ref, int compatibility_mode) {
  RefreshRunObjects();
  if (ref != nullptr && sim_ctx_ != nullptr) {
    VpiRefreshWaitedOn(
        *ref, *sim_ctx_, [this] { return AllocObject(); },
        [this](auto* proc) { return ThreadObjectFor(proc); });
  }

  ref = VpiIoDeclStandIn(ref, type);
  const VpiIterateModes kModes = ComputeVpiIterateModes(type, ref);

  if (ref && VpiReadSealed(*ref) && !kModes.tf_argument) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        VpiText("vpi_iterate() on a protected object is an error");
    return nullptr;
  }

  if (ref && ref->type == vpiCaseItem && type == vpiExpr &&
      ref->default_case_item) {
    return nullptr;
  }

  auto* iter = new VpiObject();
  iter->type = vpiIterator;
  iter->iter_ref = ref;
  iter->iter_type = type;
  iter->scan_index = 0;

  VpiIterateStores stores{all_objects_, time_queue_slots_, cb_handles_,
                          callbacks_};
  DispatchVpiIterate(type, ref, kModes, stores, iter);

  if (iter->children.empty()) {
    delete iter;
    return nullptr;
  }
  const char* unsupported =
      VpiCompatibilityUnsupportedConstruct(compatibility_mode, iter->children);
  if (unsupported != nullptr) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(unsupported);
  }
  return iter;
}

VpiHandle VpiContext::Scan(VpiHandle iterator) {
  if (!iterator) return nullptr;
  if (iterator->type != vpiIterator) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(
        "vpi_scan(): the handle is not an iterator returned from "
        "vpi_iterate()");
    return nullptr;
  }
  if (iterator->scan_index >= iterator->children.size()) {
    delete iterator;
    return nullptr;
  }
  return iterator->children[iterator->scan_index++];
}

}  // namespace delta
