#include <optional>

#include "simulator/eval_randomize_internal.h"
#include "simulator/sim_context_types.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_class_typespecs.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_coverage.h"
#include "simulator/vpi_coverage_items.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_dynamic_ranges.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_io_decl_stand_in.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_query_instance.h"
#include "simulator/vpi_query_select.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

bool VpiGetProtectedRefused(int property, VpiHandle obj) {
  const bool kExpression = VpiIsExprType(obj->type) ||
                           VpiIsNetsType(obj->type) ||
                           VpiIsVariablesType(obj->type);
  return VpiReadSealed(*obj) && property != kVpiType &&
         property != vpiIsProtected && (property != kVpiSize || !kExpression);
}

int VpiGetSize(VpiHandle obj) {
  if (obj->type == vpiGenScopeArray) return VpiGenScopeArraySize(obj);
  if (obj->queue != nullptr)
    return static_cast<int>(obj->queue->elements.size());
  if (obj->assoc != nullptr) return static_cast<int>(obj->assoc->Size());
  if (obj->type == vpiRange && VpiDynamicRangeOf(obj) != nullptr) {
    return VpiDynamicRangeSize(*obj);
  }
  if (obj->type == vpiStringVar && obj->var != nullptr) {
    return static_cast<int>(obj->var->value.width / 8);
  }
  if (obj->type == vpiStructNet || obj->type == vpiUnionNet) {
    return VpiAggregateNetSize(obj);
  }
  if (obj->type == vpiContAssignBit) return 1;
  if (obj->type == vpiPort) return VpiPortSize(obj->null_port, obj->size);
  return obj->size;
}

int VpiGetAccessType(VpiHandle obj) {
  if (obj->type == vpiConstraint)
    return obj->access_type == vpiExternAcc ? vpiExternAcc : 0;
  if (obj->type == vpiInterfaceTfDecl)
    return (obj->access_type == vpiForkJoinAcc ||
            obj->access_type == vpiExternAcc)
               ? obj->access_type
               : vpiUndefined;
  if (!VpiIsTaskFuncType(obj->type)) return vpiUndefined;
  if (obj->is_dpi) return obj->dpi_export ? vpiDPIExportAcc : vpiDPIImportAcc;
  return obj->access_type;
}

int VpiGetObjId(VpiHandle obj) {
  if (obj->type == vpiClassVar) {
    return obj->referenced_object
               ? static_cast<int>(obj->referenced_object->obj_id)
               : 0;
  }
  return static_cast<int>(obj->obj_id);
}

int VpiGetGeneric(VpiHandle obj) {
  if (obj->type != vpiRefObj) return vpiUndefined;
  bool refers_to_interface =
      obj->actual && (obj->actual->type == vpiInterface ||
                      obj->actual->type == vpiInterfaceArray);
  return VpiRefObjGeneric(refers_to_interface, obj->generic_interface);
}

int VpiGetAllocScheme(VpiHandle obj) {
  if (obj->prefix && (obj->prefix->type == vpiClassVar ||
                      obj->prefix->type == vpiVirtualInterfaceVar)) {
    return obj->prefix->alloc_scheme;
  }
  return obj->alloc_scheme;
}

int VpiGetHasActual(VpiHandle obj) {
  if (!VpiIsDynamicPrefixSourceType(obj->type)) return vpiUndefined;
  const VpiObject* bound = obj->prefix != nullptr ? obj->prefix : obj;
  int origin = obj->actual_origin;
  for (const VpiObject* at = obj;
       origin == kVpiActualBySimTime && at != nullptr; at = at->parent) {
    origin = at->actual_origin;
  }
  return VpiObjectHasActual(origin, bound->actual != nullptr) ? 1 : 0;
}

int VpiGetExpanded(VpiHandle obj) {
  if (obj->type == vpiNetBit) return VpiNetBitExpanded(obj) ? 1 : 0;
  return obj->is_vectored ? 0 : 1;
}

int VpiGetDpicStr(VpiHandle obj) {
  if (!obj->is_dpi) return 0;
  return obj->is_dpi_c ? vpiDPIC : vpiDPI;
}

int VpiGetBlocking(VpiHandle obj) {
  if (obj->type != vpiEventStmt && obj->type != vpiAssignment) {
    return vpiUndefined;
  }
  return obj->blocking ? 1 : 0;
}

bool VpiIsGenScopeLocalParam(VpiHandle obj) {
  if (obj->parent == nullptr || obj->parent->type != vpiGenScope) return false;
  return obj->type == vpiParameter;
}

int VpiGetDefAttribute(VpiHandle obj) {
  if (obj->type != vpiAttribute) return vpiUndefined;
  return obj->def_attribute ? 1 : 0;
}

int VpiGetIsDeferred(VpiHandle obj) {
  if (!VpiIsImmediateAssertionType(obj->type)) return vpiUndefined;
  return obj->is_deferred ? 1 : 0;
}

int VpiGetIsFinal(VpiHandle obj) {
  if (!VpiIsImmediateAssertionType(obj->type)) return vpiUndefined;
  return obj->is_final ? 1 : 0;
}

int VpiGetScalarOrVector(int property, VpiHandle obj) {
  const bool kScalar = property == vpiScalar;
  if (obj->type == vpiRegBit) return kScalar ? 1 : 0;
  if (VpiIsVariablesType(obj->type) || VpiIsTypespecType(obj->type)) {
    return (kScalar ? obj->decl_scalar : obj->decl_vector) ? 1 : 0;
  }
  if (VpiIsNetsType(obj->type)) return VpiNetIsScalarOrVector(kScalar, obj);
  if (!VpiScalarVectorAppliesTo(obj->type)) return 0;
  return (kScalar ? VpiPortScalar(obj->size) : VpiPortVector(obj->size)) ? 1
                                                                         : 0;
}

int VpiGetLineNo(VpiHandle obj) {
  return VpiHasLocationProperties(obj->type) ? obj->line_no : vpiUndefined;
}

int VpiGetDefLineNo(VpiHandle obj) {
  if (obj->type != vpiAttribute && !VpiIsInstanceType(obj->type)) {
    return vpiUndefined;
  }
  return obj->def_line_no;
}

int VpiGetInstanceTime(int property, VpiHandle obj) {
  if (!VpiIsInstanceType(obj->type)) return vpiUndefined;
  return property == vpiTimeUnit ? obj->time_unit : obj->time_precision;
}

int VpiBool(bool flag) { return flag ? 1 : 0; }

int VpiGetTypeRestricted(int property, VpiHandle obj, bool& handled) {
  handled = true;
  if (int instance = 0; VpiGetInstanceProperty(property, obj, instance)) {
    return instance;
  }
  if (int net = 0; VpiGetNetStrengthProperty(property, obj, net)) return net;
  switch (property) {
    case vpiObjId:
      return VpiGetObjId(obj);
    case vpiScalar:
    case vpiVector:
      return VpiGetScalarOrVector(property, obj);
    case vpiArrayType:
      return VpiIsArrayVarType(obj->type) || obj->type == vpiArrayTypespec
                 ? obj->array_type
                 : vpiUndefined;
    case vpiRandType:
      return VpiRandTypeOf(obj);
    case vpiIsRandomized:
      return VpiBool(VpiVariableIsRandomized(obj));
    case vpiStructUnionMember:
      return VpiBool(VpiVariableIsStructUnionMember(obj) ||
                     VpiNetStructUnionMember(obj));
    case vpiConstantVariable:
      return VpiBool(obj->decl_facts.constant_variable);
    case vpiNetType:
      return VpiNetTypeOf(obj);
    case vpiResolvedNetType:
      return VpiResolvedNetTypeOf(obj);
    case vpiConstantSelect:
      return VpiGetConstantSelect(obj);
    case vpiPortIndex:
      return obj->type == vpiPortBit ? vpiUndefined : obj->index;
    case vpiGeneric:
      return VpiGetGeneric(obj);
    case kVpiAllocScheme:
      return VpiGetAllocScheme(obj);
    case vpiBlocking:
      return VpiGetBlocking(obj);
    case vpiDefAttribute:
      return VpiGetDefAttribute(obj);
    case vpiDefLineNo:
      return VpiGetDefLineNo(obj);
    case vpiTimeUnit:
    case vpiTimePrecision:
      return VpiGetInstanceTime(property, obj);
    case vpiHasActual:
      return VpiGetHasActual(obj);
    case vpiIsDeferred:
      return VpiGetIsDeferred(obj);
    case vpiIsFinal:
      return VpiGetIsFinal(obj);
    case vpiExpanded:
      return VpiGetExpanded(obj);
    case vpiLineNo:
      return VpiGetLineNo(obj);
    case vpiDPICStr:
      return VpiGetDpicStr(obj);
    default:
      handled = false;
      return 0;
  }
}

int VpiGetAlwaysType(VpiHandle obj) {
  return VpiIsAlwaysType(obj->always_type) ? obj->always_type : vpiUndefined;
}

int VpiGetJoinType(VpiHandle obj) {
  return VpiIsJoinType(obj->join_type) ? obj->join_type : vpiJoin;
}

int ClockingEdge(int property, const VpiObject& obj) {
  if (obj.type != vpiClockingBlock && obj.type != vpiClockingIODecl) {
    return vpiUndefined;
  }
  return property == vpiInputEdge ? obj.input_edge : obj.output_edge;
}

int VpiGetSimplePropertyA(int property, VpiHandle obj, bool& handled) {
  handled = true;
  switch (property) {
    case kVpiType:
      return obj->type;
    case vpiIsProtected:
      return VpiBool(obj->is_protected);
    case kVpiSize:
      return VpiGetSize(obj);
    case vpiPrimType:
      return obj->prim_type;
    case vpiTermIndex:
      return obj->index;
    case kVpiDirection:
      return obj->direction;
    case vpiInputEdge:
    case vpiOutputEdge:
      return ClockingEdge(property, *obj);
    case vpiPathType:
      return obj->path_type;
    case vpiPolarity:
      return obj->polarity;
    case vpiDataPolarity:
      return obj->data_polarity;
    case vpiModPathHasIfNone:
      return VpiBool(obj->mod_path_has_if_none);
    case vpiEdge:
      return obj->edge;
    case vpiTchkType:
      return obj->tchk_type;
    case vpiPortType:
      return obj->port_type;
    case vpiExplicitName:
      return VpiBool(obj->explicit_name);
    case vpiIsModPort:
      return VpiBool(obj->is_modport);
    case vpiTopModule:
      return VpiBool(obj->top_module);
    case vpiIteratorType:
      return obj->type != vpiIterator ? vpiUndefined : obj->iter_type;
    case vpiDefDecayTime:
      return obj->def_decay_time;
    case vpiLocalParam:
      return VpiBool(obj->local_param || VpiIsGenScopeLocalParam(obj));
    case vpiConnByName:
      return VpiBool(obj->conn_by_name);
    case kVpiAutomatic:
      return VpiBool(obj->automatic || obj->type == vpiClassDefn ||
                     obj->type == vpiClassTypespec);
    case vpiOpType:
      return obj->op_type;
    case vpiAlwaysType:
      return VpiGetAlwaysType(obj);
    case vpiCaseType:
      return obj->case_type;
    case vpiQualifier:
      return obj->qualifier;
    case vpiConstType:
      return obj->const_type;
    case vpiIndexedPartSelectType:
      return obj->indexed_part_select_type;
    case vpiOpStrong:
      return VpiBool(obj->op_strong);
    case vpiActive:
      return VpiBool(obj->active);
    case vpiScheduled:
      return VpiBool(obj->scheduled);
    case vpiIsCoverSequence:
      return VpiBool(obj->cover_sequence);
    case vpiIsClockInferred:
      return VpiBool(obj->clock_inferred);
    default:
      handled = false;
      return 0;
  }
}

int VpiGetSimplePropertyB(int property, VpiHandle obj, bool& handled) {
  handled = true;
  switch (property) {
    case vpiExplicitScalared:
      return VpiBool(obj->is_scalared);
    case vpiExplicitVectored:
      return VpiBool(obj->is_vectored);
    case vpiImplicitDecl:
      return VpiBool(obj->implicit_decl);
    case vpiStartLine:
      return obj->start_line;
    case vpiColumn:
      return obj->column;
    case vpiEndLine:
      return obj->end_line;
    case vpiEndColumn:
      return obj->end_column;
    case vpiOffset:
      return obj->offset;
    case vpiNetDeclAssign:
      return VpiBool(obj->net_decl_assign);
    case vpiStrength0:
      return obj->strength0;
    case vpiStrength1:
      return obj->strength1;
    case vpiAccessType:
      return VpiGetAccessType(obj);
    case vpiDPIPure:
      return VpiBool(obj->dpi_pure);
    case vpiDPIContext:
      return VpiBool(obj->dpi_context);
    case vpiMethod:
      return VpiBool(VpiTaskFuncIsMethod(obj));
    case vpiVisibility:
      return VpiObjectVisibility(obj);
    case vpiSigned:
      return VpiBool(VpiFunctionIsSigned(obj) || obj->decl_signed);
    case vpiVirtual:
      return VpiBool(obj->is_virtual);
    case vpiIsConstraintEnabled:
      return VpiBool(
          obj->constraint_of != nullptr
              ? IsObjectConstraintActive(obj->constraint_of, obj->name)
              : obj->constraint_enabled);
    case vpiDistType:
      return obj->dist_type;
    case vpiClassType:
      return obj->type == vpiClassTypespec ? VpiClassTypeOf(*obj)
                                           : vpiUndefined;
    case vpiPacked:
      return VpiBool(obj->packed || obj->type == vpiPackedArrayVar ||
                     VpiVariableIsPackedArrayMember(obj));
    case vpiArrayMember:
      return VpiBool(
          VpiVariableIsArrayMember(obj) || VpiNetIsArrayMember(obj) ||
          ((obj->type == vpiGenScope || VpiIsInstanceType(obj->type) ||
            VpiIsPrimitiveType(obj->type)) &&
           obj->array_member));
    case vpiPackedArrayMember:
      return VpiBool(VpiNetIsPackedArrayMember(obj) ||
                     VpiVariableIsPackedArrayMember(obj));
    case vpiProtected:
    case vpiArray:
      if (obj->type != vpiGenScope) {
        handled = false;
        return 0;
      }
      return VpiBool(property == vpiArray ? obj->array_member
                                          : obj->is_protected);
    case vpiIsMemory:
      return VpiBool(VpiArrayVarIsMemory(obj));
    case vpiTagged:
      return VpiBool(obj->tagged);
    case vpiSoft:
      return VpiBool(obj->soft);
    case vpiJoinType:
      return VpiGetJoinType(obj);
    case vpiLocalVarDecls:
      return VpiBool(obj->local_var_decls);
    case vpiDelayType:
      return obj->delay_type;
    case vpiFuncType:
      return obj->func_type;
    case vpiUserDefn:
      return VpiBool(obj->user_defined);
    default:
      handled = false;
      return 0;
  }
}

int VpiGetSimpleProperty(int property, VpiHandle obj) {
  bool handled = false;
  int value = VpiGetSimplePropertyA(property, obj, handled);
  if (handled) return value;
  return VpiGetSimplePropertyB(property, obj, handled);
}

}  // namespace

int VpiContext::Get(int property, VpiHandle obj) {
  if (!obj) {
    if (property == vpiTimePrecision || property == vpiTimeUnit) {
      return SmallestModuleTimePrecision();
    }
    if (property == vpiSaveRestartID) return kVpiRunSaveRestartId;
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText("vpi_get() requires an object");
    return vpiUndefined;
  }
  obj = VpiIoDeclStandIn(obj, property);
  if (VpiGetProtectedRefused(property, obj)) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        VpiText("vpi_get() on a protected object is an error");
    return vpiUndefined;
  }
  if (obj->property_needs_side_effect_eval && property != kVpiType) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(
        "vpi_get(): this property cannot be determined without evaluating an "
        "expression with side effects");
    return vpiUndefined;
  }
  if (std::optional<int> coverage_type = CoverageTypeForVpiProperty(property)) {
    return GetCoverageControlState().CoverageGet(CoverageScopeName(obj),
                                                 *coverage_type);
  }
  if (std::optional<int> covered = VpiItemCoverage(obj, property, stmt_objects_,
                                                   GetCoverageControlState())) {
    return *covered;
  }
  if (obj->type == vpiClassVar) obj->referenced_object = ClassObjectOf(*obj);
  bool handled = false;
  int restricted = VpiGetTypeRestricted(property, obj, handled);
  if (handled) return restricted;
  return VpiGetSimpleProperty(property, obj);
}

PLI_INT64 VpiContext::Get64(int property, VpiHandle obj) {
  if (!obj) return Get(property, obj);
  if (VpiGetProtectedRefused(property, obj)) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        VpiText("vpi_get64() on a protected object is an error");
    return vpiUndefined;
  }
  switch (property) {
    case vpiObjId:
      if (obj->type == vpiClassVar) {
        const VpiObject* referenced = ClassObjectOf(*obj);
        return referenced != nullptr ? referenced->obj_id : 0;
      }
      return obj->obj_id;
    default:
      return Get(property, obj);
  }
}

int VpiContext::FreeObject(VpiHandle obj) {
  (void)obj;
  last_error_.state = kVpiPLI;
  last_error_.level = kVpiWarning;
  last_error_.message = VpiText(
      "vpi_free_object() is deprecated; use vpi_release_handle() instead");
  return 0;
}
}  // namespace delta
