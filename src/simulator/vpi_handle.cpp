#include <cstddef>
#include <cstdio>
#include <span>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/envelope_viewport.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_assertion_cb.h"
#include "simulator/vpi_class_objects.h"
#include "simulator/vpi_class_typespecs.h"
#include "simulator/vpi_collection_elements.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_constraint_relations.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_coverage_items.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_design_prefixed_refs.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_handle_instance.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_io_decl_stand_in.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_pool_keeper.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

void SetVpiHandleError(s_vpi_error_info& err, const char* message) {
  err.state = kVpiPLI;
  err.level = kVpiError;
  err.message = VpiText(message);
}

struct NamePathStep {
  VpiHandle current;
  VpiHandle scope;
  std::string_view part;
  bool is_last;
};

VpiHandle ResolveNamePathComponent(
    const NamePathStep& step,
    const std::unordered_map<std::string_view, VpiObject*>& object_map) {
  if (step.current == nullptr && step.scope == nullptr) {
    auto it = object_map.find(step.part);
    return (it == object_map.end()) ? nullptr : it->second;
  }
  VpiHandle within = (step.current == nullptr) ? step.scope : step.current;
  VpiHandle search = within;
  if (within->type == vpiClassVar && within->referenced_object) {
    search = within->referenced_object;
  }
  return ChildNamed(search, step.part);
}

bool PassesThroughSealedScope(const std::vector<VpiHandle>& path) {
  const VpiHandle kReached = path.back();
  if (kReached != nullptr &&
      kReached->viewport_access != ViewportAccess::kNone) {
    return false;
  }
  for (size_t i = 0; i + 1 < path.size(); ++i) {
    if (VpiReadSealed(*path[i])) return true;
  }
  return false;
}

}  // namespace

VpiHandle VpiContext::HandleByName(const char* name, VpiHandle scope) {
  if (!name) return nullptr;

  if (scope != nullptr && VpiReadSealed(*scope)) {
    SetVpiHandleError(
        last_error_, "vpi_handle_by_name() with a protected scope is an error");
    return nullptr;
  }

  std::vector<std::string_view> parts = VpiHandleNameComponents(name);

  std::vector<VpiHandle> path;
  VpiHandle current = nullptr;
  for (size_t i = 0; i < parts.size(); ++i) {
    bool is_last = (i + 1 == parts.size());
    NamePathStep step{current, scope, parts[i], is_last};
    current = ResolveNamePathComponent(step, object_map_);
    if (current == nullptr) break;
    if (current->type == vpiClassVar) {
      current->referenced_object = ClassObjectOf(*current);
    }
    path.push_back(current);
  }
  if (current == nullptr) path.push_back(nullptr);
  if (PassesThroughSealedScope(path)) {
    SetVpiHandleError(last_error_,
                      "vpi_handle_by_name() through a protected scope is an "
                      "error");
    return nullptr;
  }

  if (current == nullptr) return nullptr;
  if (!VpiHandleByNameAccessible(*current)) return nullptr;
  return VpiLabelledAssertionOr(current);
}

VpiHandle VpiContext::HandleByIndex(int index, VpiHandle parent) {
  if (!parent) return nullptr;

  if (VpiReadSealed(*parent)) {
    SetVpiHandleError(
        last_error_, "vpi_handle_by_index() on a protected object is an error");
    return nullptr;
  }

  if (VpiIndexesItsVarBits(*parent)) return VpiVarBitAt(*parent, index);

  if (!VpiHasAccessByIndex(parent->type)) return nullptr;

  if ((parent->queue != nullptr || parent->assoc != nullptr) && sim_ctx_) {
    return VpiCollectionElement(
        *parent, index,
        {[this] { return AllocObject(); }, VpiPoolKeeper(name_pool_),
         sim_ctx_->GetArena()});
  }
  for (auto* child : parent->children) {
    if (VpiIndexSelects(*parent, *child, index)) return child;
  }
  return nullptr;
}

VpiHandle VpiContext::HandleByMultiIndex(int num_index, const int* index_array,
                                         VpiHandle parent) {
  if (!parent) return nullptr;

  if (VpiReadSealed(*parent)) {
    SetVpiHandleError(
        last_error_,
        "vpi_handle_by_multi_index() on a protected object is an error");
    return nullptr;
  }

  if (!VpiHasAccessByIndex(parent->type)) return nullptr;

  if (num_index <= 0 || index_array == nullptr) return nullptr;

  return VpiSubobjectByIndices(
      parent,
      std::span<const int>(index_array, static_cast<std::size_t>(num_index)));
}

namespace {

bool TryResolveConnectionRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type == vpiUse && ref->type == vpiIterator) {
    out = ref->iter_ref;
    return true;
  }
  if (type == vpiExpr && VpiIsInstanceArrayType(ref->type)) {
    out = VpiInstanceArrayConnections(ref);
    return true;
  }
  if (type == vpiDelay && VpiObjectCarriesSourceDelay(ref->type)) {
    out = VpiSourceDelayExpr(ref);
    return true;
  }
  if (type == vpiExpr && ref->type == vpiIODecl) {
    out = VpiIoDeclExpr(ref);
    return true;
  }
  if (type == vpiExpr && ref->type == vpiVirtualInterfaceVar) {
    out = VpiVirtualInterfaceExpr(ref);
    return true;
  }
  if (type == vpiHighConn) {
    out = VpiHighConn(ref);
    return true;
  }
  if (type == vpiLowConn) {
    out = VpiLowConn(ref);
    return true;
  }
  return false;
}

bool TryResolveClassAndActualRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type == vpiClassObj && ref->type == vpiClassVar) {
    out = ref->referenced_object;
    return true;
  }
  if (type == vpiReturn && ref->type == vpiFunction) {
    out = ref->return_var;
    return true;
  }
  if (type == vpiActual && ref->type == vpiRefObj) {
    out = ref->actual;
    return true;
  }
  if (type == vpiActual && ref->type == vpiVirtualInterfaceVar) {
    out = ref->actual;
    return true;
  }
  if (type == vpiActual && ref->type == vpiClockingBlock) {
    out = VpiClockingBlockActual(ref);
    return true;
  }
  return false;
}

static bool TryResolveClockingSkew(int type, VpiHandle ref, VpiHandle& out) {
  if (type != vpiInputSkew && type != vpiOutputSkew) return false;
  out = type == vpiInputSkew ? ref->input_skew : ref->output_skew;
  return true;
}

static bool TryResolveClockingRelation(int type, VpiHandle ref,
                                       VpiHandle& out) {
  if (type == vpiPrefix && ref->type == vpiClockingBlock) {
    out = VpiClockingBlockPrefix(ref);
    return true;
  }
  if (type == vpiExpr && ref->type == vpiClockingIODecl) {
    out = VpiClockingIODeclExpr(ref);
    return true;
  }
  if (type == vpiTypespec && ref->type == vpiRefObj) {
    out = VpiRefObjTypespec(ref);
    return true;
  }
  if (type == vpiDefaultClocking || type == vpiGlobalClocking) {
    out = VpiScopeNamedClockingBlock(ref, type == vpiGlobalClocking);
    return true;
  }
  if (type == vpiDefaultDisableIff) {
    out = VpiScopeDefaultDisableIff(ref);
    return true;
  }
  if (type != vpiClockingEvent) return false;
  if (ref->type == vpiClockingBlock) {
    out = VpiClockingBlockClockingEvent(ref);
    return true;
  }
  if (ref->type == vpiClockedSeq || ref->type == vpiPropertySpec ||
      ref->type == vpiClockedProp) {
    out = VpiClockingEvent(ref);
    return true;
  }
  return false;
}

static bool TryResolveParentRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type != vpiParent) return false;
  if (ref->type == vpiRefObj) {
    out = VpiRefObjParent(ref);
    return true;
  }
  if (ref->type == vpiPortBit) {
    out = ref->parent;
    return true;
  }
  if (ref->type == vpiInterfaceTypespec) {
    out = VpiInterfaceTypespecParent(ref);
    return true;
  }
  if (ref->type == vpiAttribute) {
    out = ref->parent;
    return true;
  }
  if (VpiVariableIsPackedArrayMember(ref) || VpiVariableIsArrayMember(ref) ||
      VpiVariableIsStructUnionMember(ref) || VpiNetStructUnionMember(ref) ||
      ref->type == vpiVarSelect) {
    out = ref->parent;
    return true;
  }
  if (VpiNetIsArrayMember(ref)) {
    out = ref->parent;
    while (VpiNetIsArrayMember(out)) out = out->parent;
    return true;
  }
  const bool kPackedSelect =
      ref->select_dim.has_value() || ref->bit_offset >= 0;
  if (kPackedSelect && ref->parent != nullptr) {
    out = ref->parent;
    return true;
  }
  return false;
}

bool TryResolveClockingAndParentRelation(int type, VpiHandle ref,
                                         VpiHandle& out) {
  return TryResolveClockingRelation(type, ref, out) ||
         TryResolveClockingSkew(type, ref, out) ||
         TryResolveParentRelation(type, ref, out) ||
         VpiTryResolveConstraintRelation(type, ref, out);
}

static bool TryResolveTimingControlRelation(int type, VpiHandle ref,
                                            VpiHandle& out) {
  if (type == vpiDelay && ref->type == vpiDelayControl) {
    out = VpiDelayControlDelayExpr(ref);
    return true;
  }
  if (type != vpiStmt) return false;
  if (ref->type == vpiEventControl) {
    out = VpiEventControlStmt(ref);
    return true;
  }
  if (ref->type == vpiDelayControl) {
    out = VpiDelayControlStmt(ref);
    return true;
  }
  return false;
}

static bool TryResolveParameterDeclRelation(int type, VpiHandle ref,
                                            VpiHandle& out) {
  if (type == vpiTypespec && ref->type == vpiTypeParameter) {
    out = VpiTypeParameterTypespec(ref);
    return true;
  }
  if (type == vpiExpr &&
      (ref->type == vpiParameter || ref->type == vpiTypeParameter)) {
    out = VpiParameterDefaultExpr(ref);
    return true;
  }
  if (type == vpiLhs && ref->type == vpiParamAssign) {
    out = VpiParamAssignLhs(ref);
    return true;
  }
  if (ref->type != vpiParameter) return false;
  if (type == vpiLeftRange) {
    out = VpiParameterLeftRange(ref);
    return true;
  }
  if (type == vpiRightRange) {
    out = VpiParameterRightRange(ref);
    return true;
  }
  return false;
}

bool TryResolveParameterRelation(int type, VpiHandle ref, VpiHandle& out) {
  return TryResolveParameterDeclRelation(type, ref, out) ||
         TryResolveTimingControlRelation(type, ref, out);
}

bool TryResolveConditionRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type != vpiCondition) return false;
  if (ref->type == vpiEventControl) {
    out = VpiEventControlConditionExpr(ref);
    return true;
  }
  if (VpiIsWhileOrRepeatType(ref->type)) {
    out = VpiLoopConditionExpr(ref);
    return true;
  }
  if (VpiIsWaitType(ref->type)) {
    out = VpiWaitConditionExpr(ref);
    return true;
  }
  if (VpiIsIfOrIfElseType(ref->type)) {
    out = VpiIfConditionExpr(ref);
    return true;
  }
  if (ref->type == vpiFor) {
    out = VpiForConditionExpr(ref);
    return true;
  }
  if (ref->type == vpiDoWhile) {
    out = VpiDoWhileConditionExpr(ref);
    return true;
  }
  if (ref->type == vpiReturnStmt) {
    out = VpiReturnConditionExpr(ref);
    return true;
  }
  if (ref->type == vpiCaseProperty) {
    out = VpiCasePropertyConditionExpr(ref);
    return true;
  }
  if (ref->type == vpiCase) {
    out = VpiCaseConditionExpr(ref);
    return true;
  }
  if (VpiHandle condition = VpiConstraintConditionExpr(ref)) {
    out = condition;
    return true;
  }
  return false;
}

bool TryResolvePrimitiveRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type == vpiUdpDefn && ref->type == vpiUdp) {
    out = ref->udp_defn;
    return true;
  }
  if (type != vpiPrimitive) return false;
  if (ref->parent != nullptr && VpiIsPrimitiveType(ref->parent->type)) {
    out = ref->parent;
    return true;
  }
  for (auto* child : ref->children) {
    if (VpiIsPrimitiveType(child->type)) {
      out = child;
      return true;
    }
  }
  out = nullptr;
  return true;
}

bool TryResolveTypespecClassRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type == vpiExtends && ref->type == vpiClassTypespec) {
    out = VpiClassTypespecBase(*ref);
    return true;
  }
  if (type != vpiTypespec) return false;
  for (auto* child : ref->children) {
    if (!VpiIsTypespecType(child->type)) continue;
    out = child;
    return true;
  }
  return false;
}

bool TryResolveCallbackRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type != vpiCallback || !VpiIsCallbackHostType(ref->type)) return false;
  out = ref->callback;
  return true;
}

bool TryResolvePatternRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type != vpiPattern || !VpiIsPatternType(ref->type)) return false;
  out = VpiPatternOf(ref);
  return true;
}

bool TryResolveAssignLhsRhsRelation(int type, VpiHandle ref, VpiHandle& out) {
  const int kRef = ref->type;
  const bool kNamesLhs = kRef == vpiAssignment || kRef == vpiAssignStmt ||
                         kRef == vpiForce || kRef == vpiDeassign ||
                         kRef == vpiRelease || kRef == vpiAliasStmt ||
                         kRef == vpiDefParam || VpiIsContAssignKind(kRef);
  if (type == vpiLhs && kNamesLhs) {
    out = ref->lhs;
    return true;
  }
  const bool kNamesRhs = kRef == vpiAssignment || kRef == vpiAssignStmt ||
                         kRef == vpiForce || kRef == vpiAliasStmt ||
                         kRef == vpiDefParam || kRef == vpiParamAssign ||
                         VpiIsContAssignKind(kRef);
  if (type == vpiRhs && kNamesRhs) {
    out = ref->rhs;
    return true;
  }
  return false;
}

bool TryResolveElseExprStmtRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (VpiIsImmediateAssertionType(ref->type)) {
    switch (type) {
      case vpiExpr:
        out = VpiImmediateAssertionExpr(ref);
        return true;
      case vpiStmt:
        out = VpiImmediateAssertionStmt(ref);
        return true;
      case vpiElseStmt:
        out = VpiImmediateAssertionElseStmt(ref);
        return true;
      default:
        break;
    }
  }
  if (type == vpiElseStmt && ref->type == vpiOrderedWait) {
    out = VpiOrderedWaitElseStmt(ref);
    return true;
  }
  if (type == vpiElseStmt && ref->type == vpiIfElse) {
    out = VpiIfElseStmt(ref);
    return true;
  }
  if (type == vpiElseStmt && ref->type == vpiExpectStmt) {
    out = VpiExpectElseStmt(ref);
    return true;
  }
  if (type == vpiExpr && ref->type == vpiRepeatControl) {
    out = VpiRepeatControlExpr(ref);
    return true;
  }
  if (type == vpiExpr && ref->type == vpiDisable) {
    out = VpiDisableExpr(ref);
    return true;
  }
  if (type == vpiStmt && VpiIsTaskFuncType(ref->type)) {
    out = VpiTaskFuncStmt(ref);
    return true;
  }
  return false;
}

bool TryResolveAssignAndStmtRelation(int type, VpiHandle ref, VpiHandle& out) {
  return TryResolveAssignLhsRhsRelation(type, ref, out) ||
         TryResolveElseExprStmtRelation(type, ref, out) ||
         TryResolveVariableScopeRelation(type, ref, out) ||
         TryResolveStmtScopeRelation(type, ref, out);
}

bool VpiObjectHasArrayIndexRelation(int ref_type) {
  return VpiObjectIsPrimitive(ref_type) || ref_type == vpiProgram ||
         ref_type == vpiInterface || ref_type == kVpiModule ||
         ref_type == vpiGenScope;
}

bool TryResolveIndexRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type == vpiIndex && VpiObjectHasArrayIndexRelation(ref->type)) {
    out = ref->array_member ? ref->index_expr : nullptr;
    return true;
  }
  return false;
}

bool TryResolveCalledTfRelation(int type, VpiHandle ref, VpiHandle& out) {
  const bool kDecl = ref->type == vpiInterfaceTfDecl;
  const bool kTask =
      kDecl || ref->type == vpiMethodTaskCall || ref->type == vpiTaskCall;
  const bool kFunction =
      kDecl || ref->type == vpiMethodFuncCall || ref->type == vpiFuncCall;
  if (!(type == vpiTask ? kTask : type == vpiFunction && kFunction)) {
    return false;
  }
  out = ref->builtin_method ? nullptr : ref->tf_decl;
  if (kDecl && out != nullptr && out->type != type) out = nullptr;
  return true;
}

bool TryResolvePrefixWithRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type == vpiPrefix && VpiIsMethodCallType(ref->type)) {
    out = ref->tf_prefix;
    return true;
  }
  if (type == vpiPrefix && VpiIsDynamicPrefixSourceType(ref->type)) {
    out = ref->prefix;
    return true;
  }
  if (type == vpiWith && VpiIsMethodCallType(ref->type)) {
    out = ref->tf_with_method ? ref->tf_with : nullptr;
    return true;
  }
  return TryResolveCalledTfRelation(type, ref, out);
}

bool TryResolveTimingTermRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (TryResolveSpecifyRelation(type, ref, out)) return true;
  if (type == vpiInTerm && ref->type == vpiDelayDevice) {
    out = ref->in_term;
    return true;
  }
  if (type == vpiOutTerm && ref->type == vpiDelayDevice) {
    out = ref->out_term;
    return true;
  }
  if (type == vpiVariables && ref->type == vpiConstrForEach) {
    out = ref->foreach_array;
    return true;
  }
  if (type == vpiVariables && ref->type == vpiForeachStmt) {
    out = ref->foreach_array;
    return true;
  }
  return false;
}

VpiHandle ResolveModPathOwningModule(VpiHandle ref) {
  for (VpiObject* scope = ref->parent; scope; scope = scope->parent) {
    if (scope->type == vpiInterface) {
      return nullptr;
    }
    if (scope->type == kVpiModule) {
      return scope;
    }
  }
  return nullptr;
}

bool TryResolveNettypeRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type == vpiNetTypedefAlias && ref->type == vpiNettypeDecl) {
    out = ref->aliased;
    return true;
  }
  if (type == vpiTypedefAlias && VpiIsTypespecType(ref->type)) {
    out = VpiTypespecTypedefAlias(ref->aliased != nullptr, ref->aliased);
    return true;
  }
  if (type == vpiWith && ref->type == vpiNettypeDecl) {
    out = ref->nettype_with;
    return true;
  }
  return false;
}

bool TryResolveTimingAndNettypeRelation(int type, VpiHandle ref,
                                        VpiHandle& out) {
  if (TryResolveTimingTermRelation(type, ref, out)) return true;
  if (type == kVpiModule && ref->type == vpiModPath) {
    out = ResolveModPathOwningModule(ref);
    return true;
  }
  return TryResolveNettypeRelation(type, ref, out);
}

template <typename ObjectOf>
bool TryResolveDesignatedRelation(int type, VpiHandle ref,
                                  const ObjectOf& object_of, VpiHandle& out) {
  return TryResolveRunClassRelation(type, ref, object_of, out) ||
         TryResolveSelectRelation(type, ref, out) ||
         TryResolveTypespecRelation(type, ref, out) ||
         TryResolveConnectionRelation(type, ref, out) ||
         TryResolveClassAndActualRelation(type, ref, out) ||
         TryResolveClockingAndParentRelation(type, ref, out) ||
         TryResolveParameterRelation(type, ref, out) ||
         TryResolveConditionRelation(type, ref, out) ||
         TryResolveProcessAndStmtRelation(type, ref, out) ||
         TryResolveTypespecClassRelation(type, ref, out) ||
         TryResolvePatternRelation(type, ref, out) ||
         TryResolvePrimitiveRelation(type, ref, out) ||
         TryResolveAssignAndStmtRelation(type, ref, out) ||
         TryResolveIndexRelation(type, ref, out) ||
         TryResolvePrefixWithRelation(type, ref, out) ||
         TryResolveTimingAndNettypeRelation(type, ref, out) ||
         TryResolveInstanceRelation(type, ref, out) ||
         TryResolveFsmRelation(type, ref, out) ||
         TryResolveCallbackRelation(type, ref, out);
}

}  // namespace

VpiHandle VpiContext::Handle(int type, VpiHandle ref) {
  if (!ref && type == vpiFrame) return ActiveFrame();

  if (!ref && type == vpiSysTfCall) return current_systf_call_;

  if (!ref && type == vpiActiveTimeFormat) return active_time_format_call_;

  if (!ref) return nullptr;
  ref = VpiIoDeclStandIn(ref, type);

  if (VpiReadSealed(*ref)) {
    SetVpiHandleError(last_error_,
                      "vpi_handle() on a protected object is an error");
    return nullptr;
  }

  if (ref->property_needs_side_effect_eval) {
    SetVpiHandleError(
        last_error_,
        "vpi_handle(): this relation cannot be determined without evaluating "
        "an expression with side effects");
    return nullptr;
  }

  const auto kByName = [this](const std::string& scope) {
    return HandleByName(scope.c_str(), nullptr);
  };
  VpiRefreshPrefixedClockingBlock(type, *ref, sim_ctx_, kByName);
  VpiRefreshVirtualInterfaceActual(type, *ref, sim_ctx_, kByName);
  VpiHandle designated = nullptr;
  const auto kClassObjectOf = [this](VpiObject& var) {
    return ClassObjectOf(var);
  };
  if (TryResolveDesignatedRelation(type, ref, kClassObjectOf, designated)) {
    return designated;
  }

  if (ref->parent && ref->parent->type == type) return ref->parent;

  for (auto* child : ref->children) {
    if (child->type == type) return child;
  }
  return nullptr;
}

}  // namespace delta
