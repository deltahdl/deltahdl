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
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message = "vpi_handle() on a protected object is an error";
    return nullptr;
  }

  // §37.3.5: it is an error to ask for a relation of an expression when the
  // implementation cannot reach the related handle without also evaluating an
  // expression that has side effects. The traversal is refused with an error
  // and a null handle rather than triggering the side effect.
  if (ref->property_needs_side_effect_eval) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_handle(): this relation cannot be determined without evaluating "
        "an expression with side effects";
    return nullptr;
  }

  // §37.84 details 1 and 2: vpi_handle(vpiUse, iterator) recovers the reference
  // handle the iterator was created over (detail 1). When that reference was
  // null
  // - an iterator built over a null handle - the stored reference is null, so
  // the traversal hands back null in turn (detail 2). See also §38.23.
  if (type == vpiUse && ref->type == vpiIterator) return ref->iter_ref;

  // §37.11 detail 1: traversing vpiExpr from an instance array reaches the
  // operation object that lists the array's actual connections, not a child
  // whose own type happens to be vpiExpr.
  if (type == vpiExpr && VpiIsInstanceArrayType(ref->type)) {
    return VpiInstanceArrayConnections(ref);
  }

  // §37.3.4: vpiDelay of a net, primitive, module path, timing check, or
  // continuous assignment reaches the source-specified delay expression - a
  // designated expression, not a child whose own type is vpiDelay, so the
  // shared traversal below cannot find it.
  if (type == vpiDelay && VpiObjectCarriesSourceDelay(ref->type)) {
    return VpiSourceDelayExpr(ref);
  }

  // §37.13 detail 2: vpiExpr of an io decl reaches its designated connection -
  // a ref obj, virtual interface var, net, variable, or interface tf decl -
  // whose own type is not vpiExpr, so the shared traversal below cannot find
  // it.
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

  // §37.33 detail 5: vpiClassObj of a class variable reaches the class object
  // it currently references. The object is shared - several variables may
  // reference it and one variable may reference different objects over its
  // lifetime - so it is reached through a designated reference, not a child
  // found by type. A class variable holding null references nothing, so the
  // relation is NULL.
  if (type == vpiClassObj && ref->type == vpiClassVar) {
    return ref->referenced_object;
  }

  // §37.41 details 1-3: vpiReturn of a function reaches the variable that
  // captures its return value. Detail 1 makes a function contain that
  // return-capture object; detail 3 makes the relation always reach a var
  // object, even for a simple return; detail 2 makes it the implicit variable a
  // caller inspects to learn a user-defined return type. The target's own type
  // is a variable kind, not vpiReturn, so it is held as a designated pointer.
  // Gated on a function reference so the constant's other meanings (it shares a
  // value with vpiImmediateAssume) cannot reach this path. A task returns
  // nothing, so it has no return variable.
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

  // §37.48 detail 3: vpiActual of a clocking block reaches the concrete
  // clocking block selected through a virtual interface prefix, or NULL when
  // that prefix holds no value at the current simulation time.
  if (type == vpiActual && ref->type == vpiClockingBlock) {
    return VpiClockingBlockActual(ref);
  }

  // §37.48 detail 2: vpiPrefix of a clocking block reaches the virtual
  // interface var the clocking block expression is immediately prefixed by;
  // NULL when the clocking block is not a virtual-interface-prefixed
  // expression.
  if (type == vpiPrefix && ref->type == vpiClockingBlock) {
    return VpiClockingBlockPrefix(ref);
  }

  // §37.48 detail 4: vpiExpr of a clocking io decl reaches the expression or
  // ref obj the io decl names.
  if (type == vpiExpr && ref->type == vpiClockingIODecl) {
    return VpiClockingIODeclExpr(ref);
  }

  // §37.15 detail 7: a ref obj's vpiTypespec is gated on the kind of its
  // actual.
  if (type == vpiTypespec && ref->type == vpiRefObj) {
    return VpiRefObjTypespec(ref);
  }

  // §37.14 / §37.15 detail 4: vpiParent of a port bit reaches its port, and of
  // a ref obj reaches the ref obj it is a subelement of.
  if (type == vpiParent &&
      (ref->type == vpiRefObj || ref->type == vpiPortBit)) {
    return ref->parent;
  }

  // §37.30 detail 2: vpiParent of a modport interface typespec reaches the
  // interface typespec it belongs to; an interface interface typespec has none.
  if (type == vpiParent && ref->type == vpiInterfaceTypespec) {
    return VpiInterfaceTypespecParent(ref);
  }

  // §37.83: vpiParent of an attribute reaches the object the attribute is
  // attached to - the instance, net, statement, or other design object that
  // owns it. That owning object is held as the attribute's parent pointer.
  if (type == vpiParent && ref->type == vpiAttribute) {
    return ref->parent;
  }

  // §37.28 detail 2: vpiTypespec of a type parameter reaches the typespec it
  // has at the end of elaboration, returned without resolving typedef aliases.
  // The target is held as a designated pointer, so the generic walk cannot
  // serve it.
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

  // §37.28 detail 5: vpiLeftRange / vpiRightRange of a value parameter reach
  // the bounds of its explicit range, or NULL when it was declared without one.
  if (type == vpiLeftRange && ref->type == vpiParameter) {
    return VpiParameterLeftRange(ref);
  }
  if (type == vpiRightRange && ref->type == vpiParameter) {
    return VpiParameterRightRange(ref);
  }

  // §37.65 detail 1: vpiStmt of an event control reaches the statement it
  // guards, except that an event control associated with an assignment always
  // reports a null statement rather than the first statement child the generic
  // traversal below would otherwise find.
  if (type == vpiStmt && ref->type == vpiEventControl) {
    return VpiEventControlStmt(ref);
  }

  // §37.68 detail 1: vpiStmt of a delay control reaches the statement it
  // guards, except that a delay control associated with an assignment always
  // reports a null statement rather than the first statement child the generic
  // traversal below would otherwise find.
  if (type == vpiStmt && ref->type == vpiDelayControl) {
    return VpiDelayControlStmt(ref);
  }

  // §37.66: vpiCondition of a while or repeat statement reaches its controlling
  // condition expression. The condition's own type is an expression kind, not
  // the vpiCondition relation tag, so the generic traversal below cannot find
  // it. The relation is gated on the loop statement kinds so it does not also
  // serve the vpiCondition edge other diagrams draw (for instance the waits of
  // §37.67). The loop body, drawn by the diagram's unlabeled edge to a
  // statement, is reached by the generic vpiStmt traversal below and needs no
  // special case here.
  if (type == vpiCondition && VpiIsWhileOrRepeatType(ref->type)) {
    return VpiLoopConditionExpr(ref);
  }

  // §37.67: vpiCondition of a wait or ordered wait statement reaches its
  // controlling condition, which the diagram draws to either an expression or a
  // sequence instance. As with the loop statements of §37.66 above, the
  // condition's own type is an expression kind (or a sequence instance) rather
  // than the vpiCondition relation tag, so the generic traversal below cannot
  // find it. The relation is gated on the wait statement kinds so it does not
  // also serve the vpiCondition edge other diagrams draw. A wait fork draws no
  // condition edge, so the helper reports null for it. The body statement (the
  // diagram's unlabeled edge) and a wait fork's else action (vpiElseStmt) each
  // carry their relation as their own child type and are reached by the generic
  // traversal below.
  if (type == vpiCondition && VpiIsWaitType(ref->type)) {
    return VpiWaitConditionExpr(ref);
  }

  // §37.71: vpiCondition of an if or if-else statement reaches its controlling
  // condition expression. As with the loop statements above, the condition's
  // own type is an expression kind rather than the vpiCondition relation tag,
  // so the generic traversal below cannot find it. The relation is gated on the
  // conditional statement kinds so it does not also serve the vpiCondition edge
  // other diagrams draw. The then-branch body, drawn by the diagram's unlabeled
  // edge to a statement, is reached by the generic vpiStmt traversal below.
  if (type == vpiCondition && VpiIsIfOrIfElseType(ref->type)) {
    return VpiIfConditionExpr(ref);
  }

  // §37.74: vpiCondition of a for statement reaches its controlling condition
  // expression. As with the loop and conditional statements above, the
  // condition's own type is an expression kind rather than the vpiCondition
  // relation tag, so the generic traversal below cannot find it. The relation
  // is gated on the for statement kind so it does not also serve the
  // vpiCondition edge other diagrams draw. The for statement's initialization
  // and increment statements (vpiForInitStmt/vpiForIncStmt) and its body (the
  // diagram's unlabeled edge to a statement) are reached by the generic
  // traversal and iteration and need no special case here.
  if (type == vpiCondition && ref->type == vpiFor) {
    return VpiForConditionExpr(ref);
  }

  // §37.75: vpiCondition of a do-while statement reaches its controlling
  // condition expression. As with the loop and conditional statements above,
  // the condition's own type is an expression kind rather than the vpiCondition
  // relation tag, so the generic traversal below cannot find it. The relation
  // is gated on the do-while kind so it does not also serve the vpiCondition
  // edge other diagrams draw. The do-while's body (the diagram's unlabeled edge
  // to a statement) is reached by the generic vpiStmt traversal below and needs
  // no special case here.
  if (type == vpiCondition && ref->type == vpiDoWhile) {
    return VpiDoWhileConditionExpr(ref);
  }

  // §37.78: vpiCondition of a return statement reaches the value it returns -
  // the single edge the return statement diagram draws. As with the loop and
  // conditional statements above, the value's own type is an expression kind
  // rather than the vpiCondition relation tag, so the generic traversal below
  // cannot find it. The relation is gated on the return statement kind so it
  // does not also serve the vpiCondition edge other diagrams draw. A return
  // that yields no value (a void function or task return) has no expression
  // child and falls through to report null.
  if (type == vpiCondition && ref->type == vpiReturnStmt) {
    return VpiReturnConditionExpr(ref);
  }

  // §37.79: the procedural continuous assignment family - an assign statement,
  // a force, a deassign, and a release - reaches its target through vpiLhs, and
  // the two that supply a value (the assign statement and the force) reach that
  // value through vpiRhs. Each side is an expression whose own type is an
  // expression kind, not the vpiLhs / vpiRhs relation tag, so the generic walk
  // below cannot find it; both are held as designated pointers. The vpiLhs
  // relation is scoped to these four kinds so it does not disturb the vpiLhs
  // edge other diagrams draw (for instance the parameter assignment of §37.28,
  // handled above). A deassign or release draws no vpiRhs edge: it falls
  // through the rhs gate below and the generic walk reports null, since it
  // names a target but supplies no value.
  if (type == vpiLhs && (ref->type == vpiAssignStmt || ref->type == vpiForce ||
                         ref->type == vpiDeassign || ref->type == vpiRelease)) {
    return ref->lhs;
  }
  if (type == vpiRhs && (ref->type == vpiAssignStmt || ref->type == vpiForce)) {
    return ref->rhs;
  }

  // §37.76: an alias statement reaches the two sides of the alias it
  // establishes - its left-hand side expression through vpiLhs and its
  // right-hand side expression through vpiRhs. As with the procedural
  // continuous assignment family of §37.79 above, each side is an expression
  // whose own type is an expression kind rather than the vpiLhs / vpiRhs
  // relation tag, so the generic walk below cannot find it; both are held as
  // the designated lhs / rhs pointers. The relations are gated on the alias
  // statement kind so they do not disturb the vpiLhs / vpiRhs edges other
  // diagrams draw. The diagram's remaining edge, the bidirectional structural
  // link between the alias statement and the enclosing instance, is reached by
  // the generic traversal and needs no special case here.
  if (type == vpiLhs && ref->type == vpiAliasStmt) {
    return ref->lhs;
  }
  if (type == vpiRhs && ref->type == vpiAliasStmt) {
    return ref->rhs;
  }

  // §37.71: vpiElseStmt of an if-else statement reaches its else-branch body.
  // The relation is drawn only from the if-else grouping, never from a plain
  // if, so it is gated on the if-else kind. The else statement's own type is a
  // statement kind rather than the vpiElseStmt relation tag, so the generic
  // traversal below cannot find it.
  if (type == vpiElseStmt && ref->type == vpiIfElse) {
    return VpiIfElseStmt(ref);
  }

  // §37.69: vpiExpr of a repeat control reaches its count expression - the
  // repetition number of an intra-assignment repeat event control. The count's
  // own type is an expression kind, not the vpiExpr relation tag, so the
  // generic traversal below cannot find it. The relation is gated on the repeat
  // control kind so it does not disturb the vpiExpr edges other diagrams draw
  // (for instance a parameter's default, §37.28). The diagram's other edge, to
  // the event control, is reached by the generic traversal below because that
  // child's own type is vpiEventControl and so needs no special case here.
  if (type == vpiExpr && ref->type == vpiRepeatControl) {
    return VpiRepeatControlExpr(ref);
  }

  // §37.77: vpiExpr of a disable statement reaches the named scope it disables
  // - a task, function, named begin, or named fork. That scope's own type is
  // one of those scope kinds, not the vpiExpr relation tag, so the generic
  // traversal below cannot find it. The relation is gated on the plain disable
  // statement so a disable fork (vpiDisableFork), which disables the active
  // process's children and names no scope, draws no such edge and falls through
  // to report null.
  if (type == vpiExpr && ref->type == vpiDisable) {
    return VpiDisableExpr(ref);
  }

  // §37.12 detail 5: vpiStmt of a task or function reaches its body - null when
  // the task/func has no statements, the lone statement when it has one, and
  // the unnamed begin grouping them when it has more than one. The body's own
  // type is a statement kind (a begin or an atomic statement), not vpiStmt, so
  // the generic traversal below cannot find it.
  if (type == vpiStmt && VpiIsTaskFuncType(ref->type)) {
    return VpiTaskFuncStmt(ref);
  }

  // §37.12 details 2 and 3: the scope of a loop control variable is the loop
  // statement that declares it - a foreach statement always (detail 3), or a
  // for statement when that for statement is itself a scope, i.e. it declares
  // its loop variables locally (detail 2, vpiLocalVarDecls). The variable is a
  // child of the loop, so its enclosing scope is the loop object rather than
  // something the generic walk below would find. A for statement that is not a
  // scope leaves the query to the generic handling.
  if (type == vpiScope && ref->parent && VpiIsLoopControlVarType(ref->type)) {
    if (ref->parent->type == vpiForeachStmt) return ref->parent;
    if (ref->parent->type == vpiFor && ref->parent->local_var_decls) {
      return ref->parent;
    }
  }

  // §37.35 detail 4: vpiIndex from a primitive reaches the index expression
  // that locates the primitive within its primitive array. The transition is
  // only meaningful for an array-member primitive; a primitive that is not part
  // of a primitive array reports NULL here rather than letting the generic walk
  // find some other expr child.
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

  // §37.6 detail 1: vpiIndex from an interface reaches the index expression
  // that locates the interface within its instance array. As with an
  // array-member program or primitive, an interface that is not an element of
  // an instance array reports NULL here rather than letting the generic walk
  // find some other expr child.
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

  // §37.85 (figure): vpiIndex from a gen scope reaches the index expression
  // that locates the gen scope within its gen scope array. As with an
  // array-member module, program, interface, or primitive, a gen scope that is
  // not an element of a gen scope array reports NULL here rather than letting
  // the generic walk find some other expr child.
  if (type == vpiIndex && ref->type == vpiGenScope) {
    return ref->array_member ? ref->index_expr : nullptr;
  }

  // §37.42 detail 2: vpiPrefix of a method call reaches the object the method
  // is applied to (the class var "packet" in "packet.send()"). The prefix is
  // held as a designated pointer (it is an expr, not a vpiPrefix-typed child);
  // a tf call that is not a method call carries no prefix.
  if (type == vpiPrefix && VpiIsMethodCallType(ref->type)) {
    return ref->tf_prefix;
  }

  // §37.61 detail 1: vpiPrefix of a dynamically prefixed object - a simple
  // expression, part-select, indexed part-select, named event, or named event
  // array - reaches the class var, virtual interface var, or clocking block
  // that prefixes it in the source. The prefix is held as a designated pointer
  // (its own type is none of these relation tags), so the generic walk below
  // cannot serve it; an object that is not prefixed reports NULL. The relation
  // is non- NULL exactly when the object represents an expression prefixed by a
  // virtual interface or clocking block, or is all or part of a non-static
  // class property prefixed by a class var.
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

  // §37.42 detail 11: a built-in method func call has no user function object,
  // so vpiFunction reports NULL; a built-in method task call likewise reports
  // NULL for vpiTask. A user-defined (non-built-in) method call falls through
  // to the generic traversal below, which finds its function/task child.
  if (type == vpiFunction && ref->type == vpiMethodFuncCall &&
      ref->builtin_method) {
    return nullptr;
  }
  if (type == vpiTask && ref->type == vpiMethodTaskCall &&
      ref->builtin_method) {
    return nullptr;
  }

  // §37.40 detail 1: a timing check's vpiTchkRefTerm relation denotes its
  // reference event (or controlled reference event), and vpiTchkDataTerm
  // denotes its data event when the check has one. Both reach tchk term
  // objects, whose own type (vpiTchkTerm) differs from the relation enum, so
  // the generic walk below cannot find them; they are held as designated
  // pointers. A check with no data event reports NULL for vpiTchkDataTerm ("if
  // any").
  if (type == vpiTchkRefTerm && ref->type == vpiTchk) return ref->tchk_ref_term;
  if (type == vpiTchkDataTerm && ref->type == vpiTchk) {
    return ref->tchk_data_term;
  }

  // §37.45: a delay device reaches its input delay term through vpiInTerm and
  // its output delay term through vpiOutTerm. Both terms are delay term objects
  // whose own type (vpiDelayTerm) differs from the relation enum, so the
  // generic walk below cannot find them; they are held as designated pointers.
  // The relations are specific to a delay device, so they do not reach a stray
  // delay term on any other object.
  if (type == vpiInTerm && ref->type == vpiDelayDevice) return ref->in_term;
  if (type == vpiOutTerm && ref->type == vpiDelayDevice) return ref->out_term;

  // §37.38 detail 1: a foreach constraint's vpiVariables relation reaches the
  // variable that represents the array being indexed. The array variable's own
  // type is a variable kind, not the relation enum, so the generic walk below
  // cannot find it; it is held as a designated pointer. The relation is
  // specific to a foreach constraint, so it does not pick up a stray variable
  // on any other object.
  if (type == vpiVariables && ref->type == vpiConstrForEach) {
    return ref->foreach_array;
  }

  // §37.75 detail 1: a foreach statement's vpiVariables relation reaches the
  // variable being indexed - the packed array, unpacked array, or string var
  // the loop iterates over. As with the foreach constraint above, that
  // variable's own type is a variable kind rather than the relation enum, so it
  // is held as a designated pointer rather than found by the generic walk. The
  // relation is specific to a foreach statement, so it does not pick up a stray
  // variable on any other object.
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
  // reports a non-null handle to that nettype. The aliased nettype's own type
  // is vpiNetTypedef, not the relation tag, so it is kept as a designated
  // pointer rather than found by the generic walk. A nettype that is not an
  // alias has no such target and reports NULL.
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

}  // namespace delta
