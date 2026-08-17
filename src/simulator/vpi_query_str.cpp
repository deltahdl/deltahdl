// §37.3.2 and §38.35: the string-valued VPI properties, which vpi_get_str()
// answers.
//
// What makes them a group is that the answer is a name rather than a number.
// §37.3.2 has vpi_get_str(vpiType, ...) hand back the very identifier of the
// type constant as the data model diagram of §37.3 spells it, so most of this
// file is the mapping from a modelled object type or operator type onto that
// spelling, and the rest reads a name, a file, a library or a cell off the
// object. vpi_get() and vpi_get64(), which answer the integer-valued
// properties of §38.33, stay in src/simulator/vpi_query.cpp.
//
// The two were in one file, which reached 980 lines against the 1000
// assert-no-oversized-source-files in .github/workflows/deltahdl.yml fails at.
// Nothing here is called from that file and nothing here calls into it:
// VpiHasLocationProperties, the one name the two share, is declared in
// simulator/vpi_model_helpers3.h and defined in simulator/vpi_helpers_nets.cpp.

#include <cstdint>
#include <string>

#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"
#include "simulator/vpi_model_helpers3.h"

namespace delta {

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

// §37.3.2: an operation's vpiOpType is one of the additional type properties;
// its integer value names an operator constant in the vpiOpType return-value
// namespace (Annex K). This maps that value onto the spelling of its constant
// so vpi_get_str(vpiOpType, ...) can hand the name back. A value outside the
// modelled operator set yields no name (null).
static const char* VpiOpTypeConstantName(int op_type) {
  switch (op_type) {
    case vpiMinusOp:
      return "vpiMinusOp";
    case vpiPlusOp:
      return "vpiPlusOp";
    case vpiNotOp:
      return "vpiNotOp";
    case vpiBitNegOp:
      return "vpiBitNegOp";
    case vpiUnaryAndOp:
      return "vpiUnaryAndOp";
    case vpiUnaryNandOp:
      return "vpiUnaryNandOp";
    case vpiUnaryOrOp:
      return "vpiUnaryOrOp";
    case vpiUnaryNorOp:
      return "vpiUnaryNorOp";
    case vpiUnaryXorOp:
      return "vpiUnaryXorOp";
    case vpiUnaryXNorOp:
      return "vpiUnaryXNorOp";
    case vpiSubOp:
      return "vpiSubOp";
    case vpiDivOp:
      return "vpiDivOp";
    case vpiModOp:
      return "vpiModOp";
    case vpiEqOp:
      return "vpiEqOp";
    case vpiNeqOp:
      return "vpiNeqOp";
    case vpiCaseEqOp:
      return "vpiCaseEqOp";
    case vpiCaseNeqOp:
      return "vpiCaseNeqOp";
    case vpiGtOp:
      return "vpiGtOp";
    case vpiGeOp:
      return "vpiGeOp";
    case vpiLtOp:
      return "vpiLtOp";
    case vpiLeOp:
      return "vpiLeOp";
    case vpiLShiftOp:
      return "vpiLShiftOp";
    case vpiRShiftOp:
      return "vpiRShiftOp";
    case vpiAddOp:
      return "vpiAddOp";
    case vpiMultOp:
      return "vpiMultOp";
    case vpiLogAndOp:
      return "vpiLogAndOp";
    case vpiLogOrOp:
      return "vpiLogOrOp";
    case vpiBitAndOp:
      return "vpiBitAndOp";
    case vpiBitOrOp:
      return "vpiBitOrOp";
    case vpiBitXorOp:
      return "vpiBitXorOp";
    case vpiBitXNorOp:
      return "vpiBitXNorOp";
    case vpiConditionOp:
      return "vpiConditionOp";
    case vpiConcatOp:
      return "vpiConcatOp";
    case vpiMultiConcatOp:
      return "vpiMultiConcatOp";
    case vpiEventOrOp:
      return "vpiEventOrOp";
    case vpiNullOp:
      return "vpiNullOp";
    case vpiListOp:
      return "vpiListOp";
    case vpiMinTypMaxOp:
      return "vpiMinTypMaxOp";
    case vpiPosedgeOp:
      return "vpiPosedgeOp";
    case vpiNegedgeOp:
      return "vpiNegedgeOp";
    case vpiArithLShiftOp:
      return "vpiArithLShiftOp";
    case vpiArithRShiftOp:
      return "vpiArithRShiftOp";
    case vpiPowerOp:
      return "vpiPowerOp";
    default:
      return nullptr;
  }
}

// §37.3.2: besides vpiType, some objects carry an additional type property
// shown in the data model diagrams - vpiDelayType, vpiNetType, vpiOpType,
// vpiPrimType, vpiResolvedNetType, or vpiTchkType. vpi_get() reports each as an
// integer type constant, and the clause states that the *name* of that constant
// is reachable through vpi_get_str(). This resolves the string form: it reads
// the same value vpi_get() would report and maps it onto the constant's
// spelling, so the two forms stay in step. The authoritative constant set lives
// in Annex K and Annex M (§37.3.2 points there); values the simulator models
// are named here, and an unmodelled value - like an unmodelled object type in
// VpiTypeConstantName - yields no name (null), leaving room for other
// subclauses' values.
static const char* VpiAdditionalTypeConstantName(int property, VpiHandle obj) {
  switch (property) {
    case vpiOpType:
      return VpiOpTypeConstantName(obj->op_type);
    default:
      return nullptr;
  }
}

// §37.41 detail 10 / §37.15 / §37.30 / §37.36: resolves vpiDefName, whose value
// depends on the object kind - a module/UDP defn reports its own name, a ref
// obj reports its actual interface/modport name, an interface typespec reports
// its modport/interface identifier, and any other kind has no definition name.
static const char* VpiDefNameStr(VpiHandle obj) {
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
}

// §37.14 / §37.60: resolves vpiName, which does not apply to a port bit,
// prefers a port's explicit/inferred name, treats an unlabeled atomic statement
// as nameless, and otherwise hands back the stored name.
static const char* VpiNameStr(VpiHandle obj) {
  // §37.14 detail 7: vpiName does not apply to a port bit.
  if (obj->type == vpiPortBit) return nullptr;
  // §37.14 detail 8: a port returns its name - explicit name preferred,
  // then any inferred name, else NULL. The model stores one name, so an
  // unnamed (null) port yields NULL while a named port yields its name.
  if (obj->type == vpiPort) {
    return VpiPortName(obj->explicit_name, obj->name, obj->name);
  }
  // §37.60 detail 1: an atomic statement's vpiName is its label when one
  // was written, and NULL otherwise - never an empty string for an
  // unlabeled statement.
  if (VpiIsAtomicStmtType(obj->type)) {
    return obj->name.empty() ? nullptr : obj->name.data();
  }
  return obj->name.data();
}

// §37.3.3: vpiFile names the source file an object came from; an object kind
// §37.3.3 excepts (no source file) or one with no stored file yields null.
static const char* VpiFileStr(VpiHandle obj) {
  if (!VpiHasLocationProperties(obj->type)) return nullptr;
  return obj->file.empty() ? nullptr : obj->file.c_str();
}

// §37.83: vpiDefFile is drawn only on the attribute object; an attribute with
// no recorded definition file - and any other object kind - yields null.
static const char* VpiDefFileStr(VpiHandle obj) {
  if (obj->type != vpiAttribute) return nullptr;
  return obj->def_file.empty() ? nullptr : obj->def_file.c_str();
}

// §37.5: vpiLibrary names a module's library; any other object kind yields
// null.
static const char* VpiLibraryStr(VpiHandle obj) {
  if (obj->type != kVpiModule) return nullptr;
  return obj->library_name.c_str();
}

// §37.5: vpiCell names a module's cell, falling back to its own name; any other
// object kind yields null.
static const char* VpiCellStr(VpiHandle obj) {
  if (obj->type != kVpiModule) return nullptr;
  return obj->cell_name.empty() ? obj->name.data() : obj->cell_name.c_str();
}

// §37.5: vpiConfig names the configuration bound to a module; any other object
// kind yields null.
static const char* VpiConfigStr(VpiHandle obj) {
  if (obj->type != kVpiModule) return nullptr;
  return obj->config_name.c_str();
}

// §37.42 detail 9: vpiDecompile hands back a functionally equivalent call to
// the one written in the source. It is drawn on the system task/function calls;
// any other object kind, and a system call that stored no decompiled form,
// yields null rather than an empty string.
static const char* VpiDecompileStr(VpiHandle obj) {
  if (obj->type != vpiSysTaskCall && obj->type != vpiSysFuncCall)
    return nullptr;
  return obj->decompile.empty() ? nullptr : obj->decompile.c_str();
}

// §38.11: resolves the string-valued property switch for vpi_get_str(), after
// the caller has handled the null- and protected-object gating. Factored out of
// VpiContext::GetStrRaw so the entry point stays small; the per-case spec
// references are kept inline so the dispatch table stays self-documenting.
static const char* VpiGetStrRawProperty(int property, VpiHandle obj) {
  switch (property) {
    // §37.3.2: every object carries a vpiType property; queried as a string it
    // yields the name of that type constant (see 37.3 for how the names
    // derive).
    case kVpiType:
      return VpiTypeConstantName(obj->type);
    // §37.3.2: the additional type properties are string-accessible as well - a
    // vpi_get_str() on one returns the name of the constant the integer form
    // reports, per the clause's statement that these constant names can be
    // reached through vpi_get_str(). All six selectors route through the shared
    // resolver, which maps the property's value onto its spelling.
    case vpiOpType:
    case vpiDelayType:
    case vpiNetType:
    case vpiPrimType:
    case vpiResolvedNetType:
    case vpiTchkType:
      return VpiAdditionalTypeConstantName(property, obj);
    case kVpiName:
      return VpiNameStr(obj);
    // §37.3.3: vpiFile names the source file an object came from - one of the
    // two location properties, alongside vpiLineNo. It applies to every object
    // that corresponds to source text; the object kinds §37.3.3 excepts have no
    // source file and yield null regardless of any stored string. The `line
    // directive (§22.12) may shift the reported file. §37.49 stores an
    // assertion's file in the same field, and it is handed back here.
    case vpiFile:
      return VpiFileStr(obj);
    // §37.83: an attribute reports the source file of its definition through
    // the vpiDefFile string property. It is drawn only on the attribute object;
    // an attribute with no recorded definition file - and any other object kind
    // - yields null rather than an empty string.
    case vpiDefFile:
      return VpiDefFileStr(obj);
    case kVpiFullName:
      return obj->full_name.empty() ? obj->name.data() : obj->full_name.c_str();
    // §37.41 detail 10: vpiDPICIdentifier reports the C linkage name of a "DPI"
    // or "DPI-C" task or function. An object that carries no such name yields
    // null rather than an empty string.
    case vpiDPICIdentifier:
      return obj->dpi_c_identifier.empty() ? nullptr
                                           : obj->dpi_c_identifier.c_str();
    case kVpiDefName:
      return VpiDefNameStr(obj);
    case kVpiLibrary:
      return VpiLibraryStr(obj);
    case kVpiCell:
      return VpiCellStr(obj);
    case kVpiConfig:
      return VpiConfigStr(obj);
    // §37.42 detail 9: a system task or function call decompiles to a
    // functionally equivalent call through the vpiDecompile string property.
    case vpiDecompile:
      return VpiDecompileStr(obj);
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
  return VpiGetStrRawProperty(property, obj);
}
}  // namespace delta
