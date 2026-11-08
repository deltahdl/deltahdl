#include <cstddef>
#include <string>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

struct VpiConstantName {
  int value;
  const char* name;
};

template <std::size_t N>
static const char* VpiConstantNameIn(const VpiConstantName (&table)[N],
                                     int value) {
  for (const VpiConstantName& entry : table) {
    if (entry.value == value) return entry.name;
  }
  return nullptr;
}

constexpr VpiConstantName kVpiTypeNames[] = {
    {vpiAlways, "vpiAlways"},
    {vpiAssignStmt, "vpiAssignStmt"},
    {vpiAssignment, "vpiAssignment"},
    {vpiBegin, "vpiBegin"},
    {vpiCase, "vpiCase"},
    {vpiCaseItem, "vpiCaseItem"},
    {vpiConstant, "vpiConstant"},
    {vpiContAssign, "vpiContAssign"},
    {vpiDeassign, "vpiDeassign"},
    {vpiDefParam, "vpiDefParam"},
    {vpiDelayControl, "vpiDelayControl"},
    {vpiDisable, "vpiDisable"},
    {vpiEventControl, "vpiEventControl"},
    {vpiEventStmt, "vpiEventStmt"},
    {vpiFor, "vpiFor"},
    {vpiForce, "vpiForce"},
    {vpiForever, "vpiForever"},
    {vpiFork, "vpiFork"},
    {vpiFuncCall, "vpiFuncCall"},
    {vpiFunction, "vpiFunction"},
    {vpiGate, "vpiGate"},
    {vpiIf, "vpiIf"},
    {vpiIfElse, "vpiIfElse"},
    {vpiInitial, "vpiInitial"},
    {vpiIntegerVar, "vpiIntegerVar"},
    {vpiInterModPath, "vpiInterModPath"},
    {vpiIterator, "vpiIterator"},
    {vpiIODecl, "vpiIODecl"},
    {vpiMemory, "vpiMemory"},
    {vpiMemoryWord, "vpiMemoryWord"},
    {vpiModPath, "vpiModPath"},
    {vpiModule, "vpiModule"},
    {vpiNamedBegin, "vpiNamedBegin"},
    {vpiNamedEvent, "vpiNamedEvent"},
    {vpiNamedFork, "vpiNamedFork"},
    {vpiNet, "vpiNet"},
    {vpiNetBit, "vpiNetBit"},
    {vpiNullStmt, "vpiNullStmt"},
    {vpiOperation, "vpiOperation"},
    {vpiParamAssign, "vpiParamAssign"},
    {vpiParameter, "vpiParameter"},
    {vpiPartSelect, "vpiPartSelect"},
    {vpiPathTerm, "vpiPathTerm"},
    {vpiPort, "vpiPort"},
    {vpiPortBit, "vpiPortBit"},
    {vpiPrimTerm, "vpiPrimTerm"},
    {vpiRealVar, "vpiRealVar"},
    {vpiReg, "vpiReg"},
    {vpiRegBit, "vpiRegBit"},
    {vpiRelease, "vpiRelease"},
    {vpiRepeat, "vpiRepeat"},
    {vpiRepeatControl, "vpiRepeatControl"},
    {vpiSchedEvent, "vpiSchedEvent"},
    {vpiSpecParam, "vpiSpecParam"},
    {vpiSwitch, "vpiSwitch"},
    {vpiSysFuncCall, "vpiSysFuncCall"},
    {vpiSysTaskCall, "vpiSysTaskCall"},
    {vpiTableEntry, "vpiTableEntry"},
    {vpiTask, "vpiTask"},
    {vpiTaskCall, "vpiTaskCall"},
    {vpiTchk, "vpiTchk"},
    {vpiTchkTerm, "vpiTchkTerm"},
    {vpiTimeVar, "vpiTimeVar"},
    {vpiTimeQueue, "vpiTimeQueue"},
    {vpiUdp, "vpiUdp"},
    {vpiUdpDefn, "vpiUdpDefn"},
    {vpiUserSystf, "vpiUserSystf"},
    {vpiVarSelect, "vpiVarSelect"},
    {vpiWait, "vpiWait"},
    {vpiWhile, "vpiWhile"},
    {vpiAttribute, "vpiAttribute"},
    {vpiBitSelect, "vpiBitSelect"},
    {vpiCallback, "vpiCallback"},
    {vpiDelayTerm, "vpiDelayTerm"},
    {vpiDelayDevice, "vpiDelayDevice"},
    {vpiFrame, "vpiFrame"},
    {vpiGateArray, "vpiGateArray"},
    {vpiModuleArray, "vpiModuleArray"},
    {vpiPrimitiveArray, "vpiPrimitiveArray"},
    {vpiNetArray, "vpiNetArray"},
    {vpiRange, "vpiRange"},
    {vpiRegArray, "vpiRegArray"},
    {vpiSwitchArray, "vpiSwitchArray"},
    {vpiUdpArray, "vpiUdpArray"},
    {vpiContAssignBit, "vpiContAssignBit"},
    {vpiNamedEventArray, "vpiNamedEventArray"},
    {vpiIndexedPartSelect, "vpiIndexedPartSelect"},
    {vpiGenScopeArray, "vpiGenScopeArray"},
    {vpiGenScope, "vpiGenScope"},
    {vpiGenVar, "vpiGenVar"},
    {vpiPackage, "vpiPackage"},
    {vpiInterface, "vpiInterface"},
    {vpiProgram, "vpiProgram"},
    {vpiInterfaceArray, "vpiInterfaceArray"},
    {vpiProgramArray, "vpiProgramArray"},
    {vpiTypespec, "vpiTypespec"},
    {vpiModport, "vpiModport"},
    {vpiInterfaceTfDecl, "vpiInterfaceTfDecl"},
    {vpiRefObj, "vpiRefObj"},
    {vpiTypeParameter, "vpiTypeParameter"},
    {vpiLongIntVar, "vpiLongIntVar"},
    {vpiShortIntVar, "vpiShortIntVar"},
    {vpiIntVar, "vpiIntVar"},
    {vpiShortRealVar, "vpiShortRealVar"},
    {vpiByteVar, "vpiByteVar"},
    {vpiClassVar, "vpiClassVar"},
    {vpiStringVar, "vpiStringVar"},
    {vpiEnumVar, "vpiEnumVar"},
    {vpiStructVar, "vpiStructVar"},
    {vpiUnionVar, "vpiUnionVar"},
    {vpiBitVar, "vpiBitVar"},
    {vpiClassObj, "vpiClassObj"},
    {vpiChandleVar, "vpiChandleVar"},
    {vpiPackedArrayVar, "vpiPackedArrayVar"},
    {vpiVirtualInterfaceVar, "vpiVirtualInterfaceVar"},
    {vpiLongIntTypespec, "vpiLongIntTypespec"},
    {vpiShortRealTypespec, "vpiShortRealTypespec"},
    {vpiByteTypespec, "vpiByteTypespec"},
    {vpiShortIntTypespec, "vpiShortIntTypespec"},
    {vpiIntTypespec, "vpiIntTypespec"},
    {vpiClassTypespec, "vpiClassTypespec"},
    {vpiStringTypespec, "vpiStringTypespec"},
    {vpiChandleTypespec, "vpiChandleTypespec"},
    {vpiEnumTypespec, "vpiEnumTypespec"},
    {vpiEnumConst, "vpiEnumConst"},
    {vpiIntegerTypespec, "vpiIntegerTypespec"},
    {vpiTimeTypespec, "vpiTimeTypespec"},
    {vpiRealTypespec, "vpiRealTypespec"},
    {vpiStructTypespec, "vpiStructTypespec"},
    {vpiUnionTypespec, "vpiUnionTypespec"},
    {vpiBitTypespec, "vpiBitTypespec"},
    {vpiLogicTypespec, "vpiLogicTypespec"},
    {vpiArrayTypespec, "vpiArrayTypespec"},
    {vpiVoidTypespec, "vpiVoidTypespec"},
    {vpiTypespecMember, "vpiTypespecMember"},
    {vpiPackedArrayTypespec, "vpiPackedArrayTypespec"},
    {vpiSequenceTypespec, "vpiSequenceTypespec"},
    {vpiPropertyTypespec, "vpiPropertyTypespec"},
    {vpiEventTypespec, "vpiEventTypespec"},
    {vpiInterfaceTypespec, "vpiInterfaceTypespec"},
    {vpiClockingBlock, "vpiClockingBlock"},
    {vpiClockingIODecl, "vpiClockingIODecl"},
    {vpiClassDefn, "vpiClassDefn"},
    {vpiConstraint, "vpiConstraint"},
    {vpiConstraintOrdering, "vpiConstraintOrdering"},
    {vpiDistItem, "vpiDistItem"},
    {vpiAliasStmt, "vpiAliasStmt"},
    {vpiThread, "vpiThread"},
    {vpiMethodFuncCall, "vpiMethodFuncCall"},
    {vpiMethodTaskCall, "vpiMethodTaskCall"},
    {vpiAssert, "vpiAssert"},
    {vpiAssume, "vpiAssume"},
    {vpiCover, "vpiCover"},
    {vpiRestrict, "vpiRestrict"},
    {vpiDisableCondition, "vpiDisableCondition"},
    {vpiClockingEvent, "vpiClockingEvent"},
    {vpiPropertyDecl, "vpiPropertyDecl"},
    {vpiPropertySpec, "vpiPropertySpec"},
    {vpiPropertyExpr, "vpiPropertyExpr"},
    {vpiMulticlockSequenceExpr, "vpiMulticlockSequenceExpr"},
    {vpiClockedSeq, "vpiClockedSeq"},
    {vpiClockedProp, "vpiClockedProp"},
    {vpiPropertyInst, "vpiPropertyInst"},
    {vpiSequenceDecl, "vpiSequenceDecl"},
    {vpiCaseProperty, "vpiCaseProperty"},
    {vpiCasePropertyItem, "vpiCasePropertyItem"},
    {vpiSequenceInst, "vpiSequenceInst"},
    {vpiImmediateAssert, "vpiImmediateAssert"},
    {vpiImmediateAssume, "vpiImmediateAssume"},
    {vpiImmediateCover, "vpiImmediateCover"},
    {vpiReturn, "vpiReturn"},
    {vpiAnyPattern, "vpiAnyPattern"},
    {vpiTaggedPattern, "vpiTaggedPattern"},
    {vpiStructPattern, "vpiStructPattern"},
    {vpiDoWhile, "vpiDoWhile"},
    {vpiOrderedWait, "vpiOrderedWait"},
    {vpiWaitFork, "vpiWaitFork"},
    {vpiDisableFork, "vpiDisableFork"},
    {vpiExpectStmt, "vpiExpectStmt"},
    {vpiForeachStmt, "vpiForeachStmt"},
    {vpiReturnStmt, "vpiReturnStmt"},
    {vpiFinal, "vpiFinal"},
    {vpiExtends, "vpiExtends"},
    {vpiDistribution, "vpiDistribution"},
    {vpiSeqFormalDecl, "vpiSeqFormalDecl"},
    {vpiPropFormalDecl, "vpiPropFormalDecl"},
    {vpiEnumNet, "vpiEnumNet"},
    {vpiIntegerNet, "vpiIntegerNet"},
    {vpiTimeNet, "vpiTimeNet"},
    {vpiUnionNet, "vpiUnionNet"},
    {vpiShortRealNet, "vpiShortRealNet"},
    {vpiRealNet, "vpiRealNet"},
    {vpiByteNet, "vpiByteNet"},
    {vpiShortIntNet, "vpiShortIntNet"},
    {vpiIntNet, "vpiIntNet"},
    {vpiLongIntNet, "vpiLongIntNet"},
    {vpiBitNet, "vpiBitNet"},
    {vpiInterconnectNet, "vpiInterconnectNet"},
    {vpiInterconnectArray, "vpiInterconnectArray"},
    {vpiStructNet, "vpiStructNet"},
    {vpiBreak, "vpiBreak"},
    {vpiContinue, "vpiContinue"},
    {vpiPackedArrayNet, "vpiPackedArrayNet"},
    {vpiNettypeDecl, "vpiNettypeDecl"},
    {vpiConstraintExpr, "vpiConstraintExpr"},
    {vpiElseConst, "vpiElseConst"},
    {vpiImplication, "vpiImplication"},
    {vpiConstrIf, "vpiConstrIf"},
    {vpiConstrIfElse, "vpiConstrIfElse"},
    {vpiConstrForEach, "vpiConstrForEach"},
    {vpiSoftDisable, "vpiSoftDisable"},
    {vpiLetDecl, "vpiLetDecl"},
    {vpiLetExpr, "vpiLetExpr"},
};

static const char* VpiTypeConstantName(int type) {
  return VpiConstantNameIn(kVpiTypeNames, type);
}

constexpr VpiConstantName kVpiOpTypeNames[] = {
    {vpiMinusOp, "vpiMinusOp"},
    {vpiPlusOp, "vpiPlusOp"},
    {vpiNotOp, "vpiNotOp"},
    {vpiBitNegOp, "vpiBitNegOp"},
    {vpiUnaryAndOp, "vpiUnaryAndOp"},
    {vpiUnaryNandOp, "vpiUnaryNandOp"},
    {vpiUnaryOrOp, "vpiUnaryOrOp"},
    {vpiUnaryNorOp, "vpiUnaryNorOp"},
    {vpiUnaryXorOp, "vpiUnaryXorOp"},
    {vpiUnaryXNorOp, "vpiUnaryXNorOp"},
    {vpiSubOp, "vpiSubOp"},
    {vpiDivOp, "vpiDivOp"},
    {vpiModOp, "vpiModOp"},
    {vpiEqOp, "vpiEqOp"},
    {vpiNeqOp, "vpiNeqOp"},
    {vpiCaseEqOp, "vpiCaseEqOp"},
    {vpiCaseNeqOp, "vpiCaseNeqOp"},
    {vpiGtOp, "vpiGtOp"},
    {vpiGeOp, "vpiGeOp"},
    {vpiLtOp, "vpiLtOp"},
    {vpiLeOp, "vpiLeOp"},
    {vpiLShiftOp, "vpiLShiftOp"},
    {vpiRShiftOp, "vpiRShiftOp"},
    {vpiAddOp, "vpiAddOp"},
    {vpiMultOp, "vpiMultOp"},
    {vpiLogAndOp, "vpiLogAndOp"},
    {vpiLogOrOp, "vpiLogOrOp"},
    {vpiBitAndOp, "vpiBitAndOp"},
    {vpiBitOrOp, "vpiBitOrOp"},
    {vpiBitXorOp, "vpiBitXorOp"},
    {vpiBitXNorOp, "vpiBitXNorOp"},
    {vpiConditionOp, "vpiConditionOp"},
    {vpiConcatOp, "vpiConcatOp"},
    {vpiMultiConcatOp, "vpiMultiConcatOp"},
    {vpiEventOrOp, "vpiEventOrOp"},
    {vpiNullOp, "vpiNullOp"},
    {vpiListOp, "vpiListOp"},
    {vpiMinTypMaxOp, "vpiMinTypMaxOp"},
    {vpiPosedgeOp, "vpiPosedgeOp"},
    {vpiNegedgeOp, "vpiNegedgeOp"},
    {vpiArithLShiftOp, "vpiArithLShiftOp"},
    {vpiArithRShiftOp, "vpiArithRShiftOp"},
    {vpiPowerOp, "vpiPowerOp"},
    {vpiImplyOp, "vpiImplyOp"},
    {vpiNonOverlapImplyOp, "vpiNonOverlapImplyOp"},
    {vpiOverlapImplyOp, "vpiOverlapImplyOp"},
    {vpiUnaryCycleDelayOp, "vpiUnaryCycleDelayOp"},
    {vpiCycleDelayOp, "vpiCycleDelayOp"},
    {vpiIntersectOp, "vpiIntersectOp"},
    {vpiFirstMatchOp, "vpiFirstMatchOp"},
    {vpiThroughoutOp, "vpiThroughoutOp"},
    {vpiWithinOp, "vpiWithinOp"},
    {vpiRepeatOp, "vpiRepeatOp"},
    {vpiConsecutiveRepeatOp, "vpiConsecutiveRepeatOp"},
    {vpiGotoRepeatOp, "vpiGotoRepeatOp"},
    {vpiPostIncOp, "vpiPostIncOp"},
    {vpiPreIncOp, "vpiPreIncOp"},
    {vpiPostDecOp, "vpiPostDecOp"},
    {vpiPreDecOp, "vpiPreDecOp"},
    {vpiMatchOp, "vpiMatchOp"},
    {vpiCastOp, "vpiCastOp"},
    {vpiIffOp, "vpiIffOp"},
    {vpiWildEqOp, "vpiWildEqOp"},
    {vpiWildNeqOp, "vpiWildNeqOp"},
    {vpiStreamLROp, "vpiStreamLROp"},
    {vpiStreamRLOp, "vpiStreamRLOp"},
    {vpiMatchedOp, "vpiMatchedOp"},
    {vpiTriggeredOp, "vpiTriggeredOp"},
    {vpiAssignmentPatternOp, "vpiAssignmentPatternOp"},
    {vpiMultiAssignmentPatternOp, "vpiMultiAssignmentPatternOp"},
    {vpiIfOp, "vpiIfOp"},
    {vpiIfElseOp, "vpiIfElseOp"},
    {vpiCompAndOp, "vpiCompAndOp"},
    {vpiCompOrOp, "vpiCompOrOp"},
    {vpiTypeOp, "vpiTypeOp"},
    {vpiAssignmentOp, "vpiAssignmentOp"},
    {vpiAcceptOnOp, "vpiAcceptOnOp"},
    {vpiRejectOnOp, "vpiRejectOnOp"},
    {vpiSyncAcceptOnOp, "vpiSyncAcceptOnOp"},
    {vpiSyncRejectOnOp, "vpiSyncRejectOnOp"},
    {vpiOverlapFollowedByOp, "vpiOverlapFollowedByOp"},
    {vpiNonOverlapFollowedByOp, "vpiNonOverlapFollowedByOp"},
    {vpiNexttimeOp, "vpiNexttimeOp"},
    {vpiAlwaysOp, "vpiAlwaysOp"},
    {vpiEventuallyOp, "vpiEventuallyOp"},
    {vpiUntilOp, "vpiUntilOp"},
    {vpiUntilWithOp, "vpiUntilWithOp"},
    {vpiImpliesOp, "vpiImpliesOp"},
    {vpiInsideOp, "vpiInsideOp"},
};

constexpr VpiConstantName kVpiPrimTypeNames[] = {
    {vpiAndPrim, "vpiAndPrim"},           {vpiNandPrim, "vpiNandPrim"},
    {vpiNorPrim, "vpiNorPrim"},           {vpiOrPrim, "vpiOrPrim"},
    {vpiXorPrim, "vpiXorPrim"},           {vpiXnorPrim, "vpiXnorPrim"},
    {vpiBufPrim, "vpiBufPrim"},           {vpiNotPrim, "vpiNotPrim"},
    {vpiBufif0Prim, "vpiBufif0Prim"},     {vpiBufif1Prim, "vpiBufif1Prim"},
    {vpiNotif0Prim, "vpiNotif0Prim"},     {vpiNotif1Prim, "vpiNotif1Prim"},
    {vpiNmosPrim, "vpiNmosPrim"},         {vpiPmosPrim, "vpiPmosPrim"},
    {vpiCmosPrim, "vpiCmosPrim"},         {vpiRnmosPrim, "vpiRnmosPrim"},
    {vpiRpmosPrim, "vpiRpmosPrim"},       {vpiRcmosPrim, "vpiRcmosPrim"},
    {vpiRtranPrim, "vpiRtranPrim"},       {vpiRtranif0Prim, "vpiRtranif0Prim"},
    {vpiRtranif1Prim, "vpiRtranif1Prim"}, {vpiTranPrim, "vpiTranPrim"},
    {vpiTranif0Prim, "vpiTranif0Prim"},   {vpiTranif1Prim, "vpiTranif1Prim"},
    {vpiPullupPrim, "vpiPullupPrim"},     {vpiPulldownPrim, "vpiPulldownPrim"},
    {vpiSeqPrim, "vpiSeqPrim"},           {vpiCombPrim, "vpiCombPrim"},
};

constexpr VpiConstantName kVpiDelayTypeNames[] = {
    {vpiModPathDelay, "vpiModPathDelay"},
    {vpiInterModPathDelay, "vpiInterModPathDelay"},
    {vpiMIPDelay, "vpiMIPDelay"},
};

constexpr VpiConstantName kVpiTchkTypeNames[] = {
    {vpiSetup, "vpiSetup"},       {vpiHold, "vpiHold"},
    {vpiPeriod, "vpiPeriod"},     {vpiWidth, "vpiWidth"},
    {vpiSkew, "vpiSkew"},         {vpiRecovery, "vpiRecovery"},
    {vpiNoChange, "vpiNoChange"}, {vpiSetupHold, "vpiSetupHold"},
    {vpiFullskew, "vpiFullskew"}, {vpiRecrem, "vpiRecrem"},
    {vpiRemoval, "vpiRemoval"},   {vpiTimeskew, "vpiTimeskew"},
};

static const char* VpiAdditionalTypeConstantName(int property, VpiHandle obj) {
  switch (property) {
    case vpiOpType:
      return VpiConstantNameIn(kVpiOpTypeNames, obj->op_type);
    case vpiNetType:
      return VpiNetTypeConstantName(VpiNetTypeOf(obj));
    case vpiPrimType:
      return VpiConstantNameIn(kVpiPrimTypeNames, obj->prim_type);
    case vpiDelayType:
      return VpiConstantNameIn(kVpiDelayTypeNames, obj->delay_type);
    case vpiTchkType:
      return VpiConstantNameIn(kVpiTchkTypeNames, obj->tchk_type);
    default:
      return VpiNetTypeConstantName(VpiResolvedNetTypeOf(obj));
  }
}

static const char* VpiDefNameStr(VpiHandle obj) {
  if (VpiIsInstanceType(obj->type)) {
    return obj->def_name.empty() ? obj->name.data() : obj->def_name.c_str();
  }
  if (obj->type == vpiRefObj) return VpiRefObjDefName(obj);
  if (obj->type == vpiInterfaceTypespec) {
    return VpiInterfaceTypespecDefName(obj);
  }
  if (obj->type == vpiUdpDefn) return obj->name.data();
  if (VpiIsPrimitiveType(obj->type)) return obj->def_name.c_str();
  return nullptr;
}

static const char* VpiNameStr(VpiHandle obj) {
  if (obj->type == vpiPortBit) return nullptr;
  if (obj->type == vpiPort) {
    return VpiPortName(obj->explicit_name, obj->name, obj->name);
  }
  if (VpiIsAtomicStmtObject(obj)) {
    return obj->name.empty() ? nullptr : obj->name.data();
  }
  return obj->name.data();
}

static const char* VpiFileStr(VpiHandle obj) {
  if (!VpiHasLocationProperties(obj->type)) return nullptr;
  return obj->file.empty() ? nullptr : obj->file.c_str();
}

static const char* VpiDefFileStr(VpiHandle obj) {
  if (obj->type != vpiAttribute && !VpiIsInstanceType(obj->type)) {
    return nullptr;
  }
  return obj->def_file.empty() ? nullptr : obj->def_file.c_str();
}

static const char* VpiLibraryStr(VpiHandle obj) {
  if (!VpiIsInstanceType(obj->type)) return nullptr;
  return obj->library_name.c_str();
}

static const char* VpiCellStr(VpiHandle obj) {
  if (!VpiIsInstanceType(obj->type)) return nullptr;
  return obj->cell_name.empty() ? obj->def_name.c_str()
                                : obj->cell_name.c_str();
}

static const char* VpiConfigStr(VpiHandle obj) {
  if (!VpiIsInstanceType(obj->type)) return nullptr;
  return obj->config_name.c_str();
}

static const char* VpiDecompileStr(VpiHandle obj) {
  if (VpiIsVariablesType(obj->type) || VpiIsNetsType(obj->type)) {
    if (obj->decompile.empty()) {
      obj->decompile = VpiStructMemberDecompileOf(obj);
    }
    return obj->decompile.c_str();
  }
  if (!VpiIsExprType(obj->type) && obj->type != vpiSysTaskCall) return nullptr;
  return obj->decompile.empty() ? nullptr : obj->decompile.c_str();
}

static bool VpiSaveRestartReasonAllowsLocation(int reason) {
  return reason == kCbStartOfSave || reason == kCbEndOfSave ||
         reason == kCbStartOfRestart || reason == kCbEndOfRestart;
}

static const char* VpiGetStrRawProperty(int property, VpiHandle obj) {
  switch (property) {
    case kVpiType:
      return VpiTypeConstantName(obj->type);
    case vpiOpType:
    case vpiDelayType:
    case vpiNetType:
    case vpiPrimType:
    case vpiResolvedNetType:
    case vpiTchkType:
      return VpiAdditionalTypeConstantName(property, obj);
    case kVpiName:
      return VpiNameStr(obj);
    case vpiFile:
      return VpiFileStr(obj);
    case vpiDefFile:
      return VpiDefFileStr(obj);
    case kVpiFullName:
      if (VpiIsNonStaticClassDataMember(obj)) return nullptr;
      return obj->full_name.empty() ? obj->name.data() : obj->full_name.c_str();
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
    case vpiDecompile:
      return VpiDecompileStr(obj);
    default:
      return nullptr;
  }
}

PLI_BYTE8* VpiContext::GetStr(int property, VpiHandle obj) {
  const char* raw = GetStrRaw(property, obj);
  if (!raw) return nullptr;
  if (get_str_buffer_.capacity() < 256) get_str_buffer_.reserve(256);
  get_str_buffer_.assign(raw);
  return get_str_buffer_.data();
}

const char* VpiContext::GetStrRaw(int property, VpiHandle obj) {
  if (!obj) {
    if (property == vpiSaveRestartLocation &&
        VpiSaveRestartReasonAllowsLocation(current_callback_reason_) &&
        !save_restart_location_.empty()) {
      return save_restart_location_.c_str();
    }
    return nullptr;
  }
  if (VpiReadSealed(*obj) && property != kVpiType &&
      property != vpiIsProtected) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        VpiText("vpi_get_str() on a protected object is an error");
    return nullptr;
  }
  return VpiGetStrRawProperty(property, obj);
}
}  // namespace delta
