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

namespace delta {

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
  // through to the switch below while every other property records the error
  // and returns vpiUndefined, the value vpi_get() yields whenever an error
  // occurs. §37.59 detail 8 carves out one more case: a protected *expression*
  // shall still permit access to vpiSize, so that property passes through too
  // when the object is one of the expr-class kinds.
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
    // §37.3.6: every object carries a vpiIsProtected Boolean property (not
    // drawn in the data model diagrams) reporting whether the handle denotes
    // protected code; TRUE when protected, FALSE otherwise.
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
      // §37.85 detail 1: a gen scope array reports the number of elements in
      // the array - the gen scopes it holds - rather than any stored width.
      if (obj->type == vpiGenScopeArray) return VpiGenScopeArraySize(obj);
      // §37.47 detail 1: a cont assign bit models a single bit of a continuous
      // assignment, so its size is always scalar (one) regardless of any stored
      // width.
      if (obj->type == vpiContAssignBit) return 1;
      // §37.14 detail 11: a null port reports size 0; any other port reports
      // its bit width. Every other object reports its own stored size. §37.35
      // detail 1: for a primitive that stored size is its number of inputs, so
      // vpiSize returns the input count through this same path.
      if (obj->type == vpiPort) return VpiPortSize(obj->null_port, obj->size);
      return obj->size;
    // §37.36 detail 2: a UDP reports its primitive type - vpiSeqPrim for a
    // sequential UDP, vpiCombPrim for a combinational one - through
    // vpiPrimType. The udp defn carries the type code; the property hands it
    // straight back (zero for an object that bears no primitive type).
    case vpiPrimType:
      return obj->prim_type;
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
    // §37.14 detail 6: a port reports whether it is scalar (exactly one bit) or
    // a vector (more than one bit), based on its own width.
    case vpiScalar:
      if (obj->type == vpiPort) return VpiPortScalar(obj->size) ? 1 : 0;
      return 0;
    case vpiVector:
      if (obj->type == vpiPort) return VpiPortVector(obj->size) ? 1 : 0;
      return 0;
    // §37.14 detail 8: whether a port carries an explicit name.
    case vpiExplicitName:
      return obj->explicit_name ? 1 : 0;
    // §37.14 details 7 and 9: the port index gives port order (the first port
    // is 0); it does not apply to a port bit, which reports vpiUndefined.
    case vpiPortIndex:
      if (obj->type == vpiPortBit) return vpiUndefined;
      return obj->index;
    // §37.15 detail 5: a ref obj reports whether it refers to a generic
    // interface (TRUE/FALSE for an interface reference, vpiUndefined for any
    // other ref obj).
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
    // type code it was created to traverse - through the integer
    // vpiIteratorType property. A non-iterator object has no walked kind, so it
    // reports 0.
    case vpiIteratorType:
      return obj->iter_type;
    // §37.5: a module reports its default net decay time (in time units)
    // through the vpiDefDecayTime integer property.
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
    // §37.83: an attribute reports through vpiDefAttribute whether it was
    // specified on a definition rather than on an instance. The property is
    // drawn only on the attribute object, so asking any other object kind is
    // not a valid query and yields vpiUndefined; for an attribute the answer is
    // the stored Boolean.
    case vpiDefAttribute:
      if (obj->type != vpiAttribute) return vpiUndefined;
      return obj->def_attribute ? 1 : 0;
    // §37.83: an attribute reports the source line of its definition through
    // the vpiDefLineNo integer property, again drawn only on the attribute
    // object.
    case vpiDefLineNo:
      if (obj->type != vpiAttribute) return vpiUndefined;
      return obj->def_line_no;
    // §37.63 detail 1: a process reports which kind of always procedure it is
    // through vpiAlwaysType, restricted to vpiAlways/vpiAlwaysComb/vpiAlwaysFF/
    // vpiAlwaysLatch. A process carrying none of those - an initial or final
    // process, or an unset always_type - has no always type, so the property
    // reports vpiUndefined rather than handing back a value outside the four.
    case vpiAlwaysType:
      return VpiIsAlwaysType(obj->always_type) ? obj->always_type
                                               : vpiUndefined;
    // §37.61 detail 3: a dynamically prefixed object reports through
    // vpiHasActual whether it has a corresponding actual. The property is drawn
    // only on the dynamic-prefix source kinds, so asking any other object kind
    // is not a valid query and yields vpiUndefined; for a source kind the
    // answer follows the object's provenance (and, when that leaves it open,
    // whether an actual is bound at the current simulation time).
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
    // (vpiUnboundedConst for the $ used in assertion ranges, detail 4); an
    // unset constant reports zero.
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
    // §37.43/§37.44: a frame or a thread reports whether it is the active one
    // as a Boolean property (the same vpiActive property, shared by both
    // models).
    case vpiActive:
      return obj->active ? 1 : 0;
    // §38.34: a scheduled-event handle reports whether its event is still in
    // the event queue as a Boolean property; cancelling the event clears it.
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
    // §37.16 detail 21: vpiExpanded on a net bit reports the parent net's
    // value; otherwise it reports the object's own expansion (a scalared net,
    // and the default, is expanded; a vectored net is not).
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
    // §37.3.3 excepts (which have no single source line) it is not a valid
    // query and yields vpiUndefined.
    case vpiLineNo:
      if (!VpiHasLocationProperties(obj->type)) return vpiUndefined;
      return obj->line_no;
    // §37.47 detail 3: a cont assign bit reports its bit offset from the least
    // significant bit through vpiOffset. The offset is measured from the LSB,
    // so the LSB shall report zero - exactly the default this field holds.
    case vpiOffset:
      return obj->offset;
    // §37.47: a continuous assignment reports whether it is a net declaration
    // assignment through the vpiNetDeclAssign Boolean property.
    case vpiNetDeclAssign:
      return obj->net_decl_assign ? 1 : 0;
    // §37.47: a continuous assignment reports the drive strengths on its 0 and
    // 1 values through vpiStrength0 and vpiStrength1.
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
      // import. A non-DPI task or function falls through to its stored access
      // type.
      if ((obj->type == vpiFunction || obj->type == vpiTask) && obj->is_dpi)
        return obj->dpi_export ? vpiDPIExportAcc : vpiDPIImportAcc;
      return obj->access_type;
    // §37.41 detail 7: vpiDPIPure reports TRUE for a pure DPI import function
    // and FALSE otherwise - the value of the stored flag, which is set only for
    // such a function.
    case vpiDPIPure:
      return obj->dpi_pure ? 1 : 0;
    // §37.41 detail 8: vpiDPIContext reports TRUE for a context import DPI task
    // or function and FALSE otherwise.
    case vpiDPIContext:
      return obj->dpi_context ? 1 : 0;
    // §37.41 detail 9: vpiDPICStr reports vpiDPIC for a "DPI-C" task or
    // function and vpiDPI for a "DPI" task or function. A task or function that
    // is not a DPI tf carries no such flavor, so the property is meaningful
    // only when is_dpi is set; report zero (none) otherwise.
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
    // property; this is exactly the condition under which the for statement is
    // a scope.
    case vpiLocalVarDecls:
      return obj->local_var_decls ? 1 : 0;
    // §37.45: a delay device and a delay term both report the kind of delay
    // they model through the vpiDelayType integer property. The value is the
    // stored delay-type code; objects that are neither carry zero and so report
    // zero.
    case vpiDelayType:
      return obj->delay_type;
    default:
      return 0;
  }
}

// §38.7: vpi_get64() returns the value of a 64-bit integer object property -
// one whose type is PLI_INT64. The value any given property carries (and, for
// those with a defined value, the value reported) is fixed by the subclause
// that introduces the property and by Annex K and Annex M; this routine
// provides the shared full-width access path and the error behaviour those
// properties rely on.
PLI_INT64 VpiContext::Get64(int property, VpiHandle obj) {
  if (!obj) return 0;
  // §38.7: as with vpi_get(), unless otherwise specified querying a property of
  // a protected object is an error, and on any error vpi_get64() returns
  // vpiUndefined. The vpiType and vpiIsProtected properties stay accessible for
  // every object, and a protected expression still permits vpiSize, mirroring
  // the carve-outs vpi_get() applies (§37.3.6, §37.59).
  if (obj->is_protected && property != kVpiType && property != vpiIsProtected &&
      !(property == kVpiSize && VpiIsExprType(obj->type))) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message = "vpi_get64() on a protected object is an error";
    return vpiUndefined;
  }
  switch (property) {
    // §37.33: a class object's unique identifier is a genuinely 64-bit value,
    // and a class variable reports the identifier of the object it references
    // (0 when it references none). vpi_get64() hands back the full width, where
    // vpi_get() must narrow the same value to PLI_INT32.
    case vpiObjId:
      if (obj->type == vpiClassVar) {
        return obj->referenced_object ? obj->referenced_object->obj_id : 0;
      }
      return obj->obj_id;
    // Every other property is a 32-bit integer or Boolean property; widen the
    // value vpi_get() computes to the 64-bit return type so vpi_get64() can
    // read it too.
    default:
      return Get(property, obj);
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
  // §38.11: vpi_get_str() returns string property values. The value is placed
  // in a single temporary buffer reused by every call - so a pointer from an
  // earlier call is overwritten by the next - and that buffer is distinct from
  // str_pool_, the storage for s_vpi_value strings. A null raw result (null or
  // protected object, or a property with no string) yields null, not "".
  const char* raw = GetStrRaw(property, obj);
  if (!raw) return nullptr;
  // Reserve once so repeated assigns of typical-length strings keep writing
  // into the same allocation, leaving an earlier returned pointer valid until
  // the next call overwrites its contents.
  if (get_str_buffer_.capacity() < 256) get_str_buffer_.reserve(256);
  get_str_buffer_.assign(raw);
  return get_str_buffer_.c_str();
}

const char* VpiContext::GetStrRaw(int property, VpiHandle obj) {
  if (!obj) return nullptr;
  // §37.3.6: a protected object's properties are inaccessible unless otherwise
  // specified, so a string query for one is an error. The vpiType and
  // vpiIsProtected properties are the exception - permitted for all objects -
  // so they fall through; any other property records the error and yields no
  // string.
  if (obj->is_protected && property != kVpiType && property != vpiIsProtected) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message = "vpi_get_str() on a protected object is an error";
    return nullptr;
  }
  switch (property) {
    // §37.3.2: every object carries a vpiType property; queried as a string it
    // yields the name of that type constant (see 37.3 for how the names
    // derive).
    case kVpiType:
      return VpiTypeConstantName(obj->type);
    case kVpiName:
      // §37.14 detail 7: vpiName does not apply to a port bit.
      if (obj->type == vpiPortBit) return nullptr;
      // §37.14 detail 8: a port returns its name - explicit name preferred,
      // then any inferred name, else NULL. The model stores one name, so an
      // unnamed (null) port yields NULL while a named port yields its name.
      if (obj->type == vpiPort) {
        return VpiPortName(obj->explicit_name, obj->name.data(),
                           obj->name.data());
      }
      // §37.60 detail 1: an atomic statement's vpiName is its label when one
      // was written, and NULL otherwise - never an empty string for an
      // unlabeled statement.
      if (VpiIsAtomicStmtType(obj->type)) {
        return obj->name.empty() ? nullptr : obj->name.data();
      }
      return obj->name.data();
    // §37.3.3: vpiFile names the source file an object came from - one of the
    // two location properties, alongside vpiLineNo. It applies to every object
    // that corresponds to source text; the object kinds §37.3.3 excepts have no
    // source file and yield null regardless of any stored string. The `line
    // directive (§22.12) may shift the reported file. §37.49 stores an
    // assertion's file in the same field, and it is handed back here.
    case vpiFile:
      if (!VpiHasLocationProperties(obj->type)) return nullptr;
      return obj->file.empty() ? nullptr : obj->file.c_str();
    // §37.83: an attribute reports the source file of its definition through
    // the vpiDefFile string property. It is drawn only on the attribute object;
    // an attribute with no recorded definition file - and any other object kind
    // - yields null rather than an empty string.
    case vpiDefFile:
      if (obj->type != vpiAttribute) return nullptr;
      return obj->def_file.empty() ? nullptr : obj->def_file.c_str();
    case kVpiFullName:
      return obj->full_name.empty() ? obj->name.data() : obj->full_name.c_str();
    // §37.41 detail 10: vpiDPICIdentifier reports the C linkage name of a "DPI"
    // or "DPI-C" task or function. An object that carries no such name yields
    // null rather than an empty string.
    case vpiDPICIdentifier:
      return obj->dpi_c_identifier.empty() ? nullptr
                                           : obj->dpi_c_identifier.c_str();
    case kVpiDefName:
      if (obj->type == kVpiModule) return obj->name.data();
      // §37.15 detail 6: a ref obj whose actual is an interface or modport
      // reports that interface's definition name or the modport name.
      if (obj->type == vpiRefObj) return VpiRefObjDefName(obj);
      // §37.30 detail 1: an interface typespec reports the modport identifier
      // or the interface declaration's identifier as its definition name.
      if (obj->type == vpiInterfaceTypespec) {
        return VpiInterfaceTypespecDefName(obj);
      }
      // §37.36: a udp defn reports its definition name - the UDP declaration's
      // identifier - through vpiDefName.
      if (obj->type == vpiUdpDefn) return obj->name.data();
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

int VpiContext::FreeObject(VpiHandle obj) {
  // Annex C.2.4: vpi_free_object() has been deprecated. Once its behavior was
  // settled against handle validity and the dynamic data of the SystemVerilog
  // object model, the routine was renamed vpi_release_handle(), so the old name
  // no longer denotes a supported operation. A surviving call to it is flagged
  // as deprecated - pointing the program at the replacement - and performs no
  // release, reporting failure.
  (void)obj;
  last_error_.state = kVpiWarning;
  last_error_.level = kVpiWarning;
  last_error_.message =
      "vpi_free_object() is deprecated; use vpi_release_handle() instead";
  return 0;
}
}  // namespace delta
