#include <algorithm>
#include <cctype>
#include <cmath>
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <string>
#include <string_view>
#include <unordered_map>
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

namespace {

// Records a VPI error (state, level, and message) on the supplied error slot,
// matching the §38.2 convention used throughout the handle-resolution routines.
void SetVpiHandleError(VpiErrorInfo& err, const char* message) {
  err.state = kVpiError;
  err.level = kVpiError;
  err.message = message;
}

// §38.21: one position in a hierarchical-name walk. A hierarchical name is
// resolved one path component at a time, so each step is described by the
// already-resolved enclosing scope (current, null before the first component),
// the caller-supplied search scope (scope, used to root the outermost
// component), the component name being resolved (part), and whether it is the
// rightmost/terminal component (is_last, which governs the protected-scope
// rule). These travel together as one entity through the resolution routines.
struct NamePathStep {
  VpiHandle current;
  VpiHandle scope;
  std::string_view part;
  bool is_last;
};

// §38.21: resolve a single path component of a hierarchical name to its handle.
// With no enclosing scope yet, the outermost component is searched from the top
// level of the design hierarchy (the object map); otherwise the search is
// confined to the immediate contents of the current/supplied scope. Returns the
// resolved handle, or null when the component names nothing.
VpiHandle ResolveNamePathComponent(
    const NamePathStep& step,
    const std::unordered_map<std::string_view, VpiObject*>& object_map) {
  if (step.current == nullptr && step.scope == nullptr) {
    // §38.21: with no scope the outermost component is searched for from the
    // top level of the design hierarchy.
    auto it = object_map.find(step.part);
    return (it == object_map.end()) ? nullptr : it->second;
  }
  // §38.21: within a scope - the supplied scope for the first component, or
  // the previously resolved scope for a deeper one - the search is confined
  // to that scope's immediate contents and nothing outside it.
  VpiHandle within = (step.current == nullptr) ? step.scope : step.current;
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
    if (child->name == step.part) {
      return child;
    }
  }
  return nullptr;
}

// §38.21: resolve one path component during a hierarchical name lookup and
// enforce the protected-scope rule on it. Returns the resolved handle for the
// component, or null when the component names nothing or when descending into
// an intermediate protected object would be required (the latter records an
// error via the supplied error slot). The handle is null on every failure path,
// so the caller stops the walk whenever this returns null.
VpiHandle ResolveNamePathStep(
    const NamePathStep& step,
    const std::unordered_map<std::string_view, VpiObject*>& object_map,
    VpiErrorInfo& err) {
  VpiHandle next = ResolveNamePathComponent(step, object_map);
  if (next == nullptr) return nullptr;

  // §38.21: a hierarchical name that passes through a protected scope is an
  // error - an intermediate component naming a protected object cannot be
  // descended into to reach a deeper object.
  if (!step.is_last && next->is_protected) {
    SetVpiHandleError(err,
                      "vpi_handle_by_name() through a protected scope is an "
                      "error");
    return nullptr;
  }
  return next;
}

}  // namespace

VpiHandle VpiContext::HandleByName(const char* name, VpiHandle scope) {
  if (!name) return nullptr;

  // §38.21: a protected object cannot serve as the search scope. Unless
  // otherwise specified, asking for a handle relative to a protected scope is
  // an error; record it and return no handle.
  if (scope != nullptr && scope->is_protected) {
    SetVpiHandleError(
        last_error_, "vpi_handle_by_name() with a protected scope is an error");
    return nullptr;
  }

  // §38.21: the name may be simple or hierarchical, so resolve it one path
  // component at a time from the leftmost (outermost) scope to the rightmost.
  std::vector<std::string_view> parts = VpiNamePathComponents(name);

  VpiHandle current = nullptr;
  for (size_t i = 0; i < parts.size(); ++i) {
    bool is_last = (i + 1 == parts.size());
    NamePathStep step{current, scope, parts[i], is_last};
    VpiHandle next = ResolveNamePathStep(step, object_map_, last_error_);
    if (next == nullptr) return nullptr;
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
    SetVpiHandleError(
        last_error_, "vpi_handle_by_index() on a protected object is an error");
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
    SetVpiHandleError(
        last_error_,
        "vpi_handle_by_multi_index() on a protected object is an error");
    return nullptr;
  }

  // §38.20: the reference object must carry the access-by-index property - the
  // same property vpi_handle_by_index() requires of its reference object.
  if (!VpiHasAccessByIndex(parent->type)) return nullptr;

  // §38.20: num_index gives how many indices index_array carries. With no
  // indices there is no index select expression to construct, so no subobject
  // is named.
  if (num_index <= 0 || index_array == nullptr) return nullptr;

  // §38.20: apply the indices in the order provided - leftmost first -
  // following the array dimension declaration from the leftmost to the
  // rightmost range of the reference handle, with an optional trailing
  // bit-select index. Each step descends to the subobject carrying that index.
  // If any index names no subobject the chain is not a legal SystemVerilog
  // index select expression, so the result is a null handle.
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

namespace {

// The branches below resolve a single vpi_handle() relation that is held as a
// designated pointer on the reference object (rather than reachable by the
// generic child/parent walk). Each helper preserves the exact original branch
// order and semantics: when a branch matches it writes the resolved handle to
// `out` and returns true; otherwise it returns false so the caller continues
// with the next group, finally falling through to the generic traversal. `ref`
// is guaranteed non-null and non-protected by the caller.

// §37.11/§37.13/§37.29/§37.84/§37.3.4 and §37.14/§37.15: connection and
// designated-expression relations of iterators, instance arrays, io decls,
// virtual interface vars, source-delay carriers, and ports.
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

// §37.33/§37.41/§37.15/§37.29/§37.48: the class object a class var references,
// a function's return variable, and the vpiActual of ref objs, virtual
// interface vars, and clocking blocks.
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

// §37.48/§37.56/§37.15/§37.14/§37.30/§37.83: a clocking block's prefix and
// clocking event, a clocked seq's clocking event, a clocking io decl's expr, a
// ref obj's typespec, and vpiParent of port bits, ref objs, modport interface
// typespecs, and attributes.
bool TryResolveClockingAndParentRelation(int type, VpiHandle ref,
                                         VpiHandle& out) {
  if (type == vpiPrefix && ref->type == vpiClockingBlock) {
    out = VpiClockingBlockPrefix(ref);
    return true;
  }
  if (type == vpiExpr && ref->type == vpiClockingIODecl) {
    out = VpiClockingIODeclExpr(ref);
    return true;
  }
  if (type == vpiClockingEvent && ref->type == vpiClockingBlock) {
    out = VpiClockingBlockClockingEvent(ref);
    return true;
  }
  if (type == vpiClockingEvent && ref->type == vpiClockedSeq) {
    // §37.56: a clocked seq within a multiclock sequence expression reaches its
    // clocking event through vpiClockingEvent, the same relation a property
    // spec and a clocked property use. Serve it through the public vpi_handle
    // path so a client walking the clocked-seq members can reach each one's
    // clock.
    out = VpiClockingEvent(ref);
    return true;
  }
  if (type == vpiTypespec && ref->type == vpiRefObj) {
    out = VpiRefObjTypespec(ref);
    return true;
  }
  if (type == vpiParent &&
      (ref->type == vpiRefObj || ref->type == vpiPortBit)) {
    out = ref->parent;
    return true;
  }
  if (type == vpiParent && ref->type == vpiInterfaceTypespec) {
    out = VpiInterfaceTypespecParent(ref);
    return true;
  }
  if (type == vpiParent && ref->type == vpiAttribute) {
    out = ref->parent;
    return true;
  }
  return false;
}

// §37.28/§37.65/§37.68: type/value parameter typespecs, defaults, ranges, the
// lhs of a param assign, the guarded statement of event/delay controls, and the
// delay expression a delay control reaches through vpiDelay.
bool TryResolveParameterRelation(int type, VpiHandle ref, VpiHandle& out) {
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
  if (type == vpiLeftRange && ref->type == vpiParameter) {
    out = VpiParameterLeftRange(ref);
    return true;
  }
  if (type == vpiRightRange && ref->type == vpiParameter) {
    out = VpiParameterRightRange(ref);
    return true;
  }
  if (type == vpiStmt && ref->type == vpiEventControl) {
    out = VpiEventControlStmt(ref);
    return true;
  }
  if (type == vpiStmt && ref->type == vpiDelayControl) {
    out = VpiDelayControlStmt(ref);
    return true;
  }
  if (type == vpiDelay && ref->type == vpiDelayControl) {
    out = VpiDelayControlDelayExpr(ref);
    return true;
  }
  return false;
}

// §37.65/§37.66/§37.67/§37.71/§37.74/§37.75/§37.78/§37.52: the controlling
// condition expression of event control, loop, wait, if, for, do-while, and
// return statements, and the expression a case property selects on.
bool TryResolveConditionRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type == vpiCondition && ref->type == vpiEventControl) {
    out = VpiEventControlConditionExpr(ref);
    return true;
  }
  if (type == vpiCondition && VpiIsWhileOrRepeatType(ref->type)) {
    out = VpiLoopConditionExpr(ref);
    return true;
  }
  if (type == vpiCondition && VpiIsWaitType(ref->type)) {
    out = VpiWaitConditionExpr(ref);
    return true;
  }
  if (type == vpiCondition && VpiIsIfOrIfElseType(ref->type)) {
    out = VpiIfConditionExpr(ref);
    return true;
  }
  if (type == vpiCondition && ref->type == vpiFor) {
    out = VpiForConditionExpr(ref);
    return true;
  }
  if (type == vpiCondition && ref->type == vpiDoWhile) {
    out = VpiDoWhileConditionExpr(ref);
    return true;
  }
  if (type == vpiCondition && ref->type == vpiReturnStmt) {
    out = VpiReturnConditionExpr(ref);
    return true;
  }
  if (type == vpiCondition && ref->type == vpiCaseProperty) {
    out = VpiCasePropertyConditionExpr(ref);
    return true;
  }
  return false;
}

// §37.79/§37.76: the lhs/rhs of the procedural continuous assignment family
// (assign/force/deassign/release) and of alias statements.
bool TryResolveAssignLhsRhsRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type == vpiLhs && (ref->type == vpiAssignStmt || ref->type == vpiForce ||
                         ref->type == vpiDeassign || ref->type == vpiRelease)) {
    out = ref->lhs;
    return true;
  }
  if (type == vpiRhs && (ref->type == vpiAssignStmt || ref->type == vpiForce)) {
    out = ref->rhs;
    return true;
  }
  if (type == vpiLhs && ref->type == vpiAliasStmt) {
    out = ref->lhs;
    return true;
  }
  if (type == vpiRhs && ref->type == vpiAliasStmt) {
    out = ref->rhs;
    return true;
  }
  return false;
}

// §37.71/§37.69/§37.77: an if-else's else branch, the expressions of repeat
// controls and disables, and a task/func body statement.
bool TryResolveElseExprStmtRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type == vpiElseStmt && ref->type == vpiIfElse) {
    out = VpiIfElseStmt(ref);
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

// §37.12: the enclosing scope of a loop control variable - the foreach
// statement that owns it, or the for statement when it declares its own loop
// variables.
bool TryResolveLoopControlScopeRelation(int type, VpiHandle ref,
                                        VpiHandle& out) {
  if (type == vpiScope && ref->parent && VpiIsLoopControlVarType(ref->type)) {
    if (ref->parent->type == vpiForeachStmt) {
      out = ref->parent;
      return true;
    }
    if (ref->parent->type == vpiFor && ref->parent->local_var_decls) {
      out = ref->parent;
      return true;
    }
  }
  return false;
}

// §37.79/§37.76/§37.71/§37.69/§37.77/§37.12: the lhs/rhs of the procedural
// continuous assignment family and alias statements, an if-else's else branch,
// repeat-control and disable expressions, a task/func body, and a loop control
// variable's enclosing scope.
bool TryResolveAssignAndStmtRelation(int type, VpiHandle ref, VpiHandle& out) {
  return TryResolveAssignLhsRhsRelation(type, ref, out) ||
         TryResolveElseExprStmtRelation(type, ref, out) ||
         TryResolveLoopControlScopeRelation(type, ref, out);
}

// §37.35/§37.9/§37.6/§37.5/§37.85: the reference object types whose vpiIndex
// relation reaches the index expression locating them within an array - a
// primitive, program, interface, module, or gen scope.
bool VpiObjectHasArrayIndexRelation(int ref_type) {
  return VpiObjectIsPrimitive(ref_type) || ref_type == vpiProgram ||
         ref_type == vpiInterface || ref_type == kVpiModule ||
         ref_type == vpiGenScope;
}

// §37.35/§37.9/§37.6/§37.5/§37.85: vpiIndex from a primitive, program,
// interface, module, or gen scope reaches the index expression that locates it
// within its array (NULL when it is not an array member).
bool TryResolveIndexRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type == vpiIndex && VpiObjectHasArrayIndexRelation(ref->type)) {
    out = ref->array_member ? ref->index_expr : nullptr;
    return true;
  }
  return false;
}

// §37.42/§37.61: a method call's prefix and with-clause, a dynamically
// prefixed object's prefix, and the NULL function/task of a built-in method
// call.
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
  if (type == vpiFunction && ref->type == vpiMethodFuncCall &&
      ref->builtin_method) {
    out = nullptr;
    return true;
  }
  if (type == vpiTask && ref->type == vpiMethodTaskCall &&
      ref->builtin_method) {
    out = nullptr;
    return true;
  }
  return false;
}

// §37.40/§37.45/§37.39: a timing check's ref/data terms, a delay device's
// in/out terms, and a foreach constraint/statement's array variable.
bool TryResolveTimingTermRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type == vpiTchkRefTerm && ref->type == vpiTchk) {
    out = ref->tchk_ref_term;
    return true;
  }
  if (type == vpiTchkDataTerm && ref->type == vpiTchk) {
    out = ref->tchk_data_term;
    return true;
  }
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

// §37.38: a mod path's owning module - the nearest enclosing module scope, or
// NULL when an interface scope intervenes first.
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

// §37.23: a nettype declaration's alias and resolution (with) function.
bool TryResolveNettypeRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type == vpiNetTypedefAlias && ref->type == vpiNetTypedef) {
    out = ref->nettype_alias;
    return true;
  }
  if (type == vpiWith && ref->type == vpiNetTypedef) {
    out = ref->nettype_with;
    return true;
  }
  return false;
}

// §37.40/§37.45/§37.38/§37.75/§37.39/§37.23: a timing check's ref/data terms, a
// delay device's in/out terms, a foreach constraint/statement's array variable,
// a mod path's owning module, and a nettype declaration's alias and resolution
// function.
bool TryResolveTimingAndNettypeRelation(int type, VpiHandle ref,
                                        VpiHandle& out) {
  if (TryResolveTimingTermRelation(type, ref, out)) return true;
  if (type == kVpiModule && ref->type == vpiModPath) {
    out = ResolveModPathOwningModule(ref);
    return true;
  }
  return TryResolveNettypeRelation(type, ref, out);
}

// §37.10 detail 3: vpi_handle(vpiInstance, obj) resolves to the immediate
// enclosing instance - the nearest package, module, interface, or program the
// object is instantiated in. The relation is not stored as a designated pointer
// on the object; it is derived by walking outward through the scope chain, so
// it is resolved here rather than by the generic single-level parent/child walk
// below (which would miss any intervening non-instance scope such as a named
// begin block). A null result is the correct answer when no instance encloses
// the object, so this always claims the relation.
bool TryResolveInstanceRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (type == vpiInstance) {
    out = VpiInstanceOf(ref);
    return true;
  }
  return false;
}

// Runs the designated-pointer relation groups in their original order, stopping
// at the first group that resolves the relation. Returns true (with the result
// in `out`) when one fired; false when none did, leaving the caller to fall
// back on the generic child/parent traversal.
bool TryResolveDesignatedRelation(int type, VpiHandle ref, VpiHandle& out) {
  return TryResolveConnectionRelation(type, ref, out) ||
         TryResolveClassAndActualRelation(type, ref, out) ||
         TryResolveClockingAndParentRelation(type, ref, out) ||
         TryResolveParameterRelation(type, ref, out) ||
         TryResolveConditionRelation(type, ref, out) ||
         TryResolveAssignAndStmtRelation(type, ref, out) ||
         TryResolveIndexRelation(type, ref, out) ||
         TryResolvePrefixWithRelation(type, ref, out) ||
         TryResolveTimingAndNettypeRelation(type, ref, out) ||
         TryResolveInstanceRelation(type, ref, out);
}

}  // namespace

VpiHandle VpiContext::Handle(int type, VpiHandle ref) {
  // §37.43 detail 4: there is at most one active frame at a time in a given
  // thread, and an application reaches it with vpi_handle(vpiFrame, NULL).
  if (!ref && type == vpiFrame) return active_frame_;

  // §37.42 detail 3: the system task or function that invoked the application
  // is reached with vpi_handle(vpiSysTfCall, NULL).
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
    SetVpiHandleError(last_error_,
                      "vpi_handle() on a protected object is an error");
    return nullptr;
  }

  // §37.3.5: it is an error to ask for a relation of an expression when the
  // implementation cannot reach the related handle without also evaluating an
  // expression that has side effects. The traversal is refused with an error
  // and a null handle rather than triggering the side effect.
  if (ref->property_needs_side_effect_eval) {
    SetVpiHandleError(
        last_error_,
        "vpi_handle(): this relation cannot be determined without evaluating "
        "an expression with side effects");
    return nullptr;
  }

  // §37.3.4 through §37.85: every relation that is held on the reference object
  // as a designated pointer (rather than reachable by the generic child/parent
  // walk below) is resolved here, in the original spec-order. Each grouped
  // helper documents the §37.x details for the relations it serves. When one
  // matches, its (possibly null) result is the answer; otherwise the lookup
  // falls through to the generic traversal.
  VpiHandle designated = nullptr;
  if (TryResolveDesignatedRelation(type, ref, designated)) return designated;

  if (ref->parent && ref->parent->type == type) return ref->parent;

  for (auto* child : ref->children) {
    if (child->type == type) return child;
  }
  return nullptr;
}

// ===========================================================================
// §37.21 Variable drivers and loads.
// ===========================================================================

}  // namespace delta
