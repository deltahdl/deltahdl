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

#include <cstddef>
#include <string>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

// A constant of one of the sets §37.3.2 names through vpi_get_str(), with its
// spelling.
struct VpiConstantName {
  int value;
  const char* name;
};

// The spelling `table` gives the constant `value`, or null for a value it does
// not list.
template <std::size_t N>
static const char* VpiConstantNameIn(const VpiConstantName (&table)[N],
                                     int value) {
  for (const VpiConstantName& entry : table) {
    if (entry.value == value) return entry.name;
  }
  return nullptr;
}

// §37.3.2: vpi_get_str(vpiType, ...) hands back the name of the type constant,
// and that name is derived from the object's name in the data model diagram
// (§37.3) - i.e. it is the very identifier of the type constant. These are the
// object types the OBJECT TYPES sections of Annex K (vpi_user.h) and Annex M
// (sv_vpi_user.h) define, each under its own spelling. Where two constants
// share a value - vpiLogicNet and vpiNet, vpiArrayNet and vpiNetArray (§37.16
// details 27 and 29), vpiLogicVar and vpiReg, vpiVarBit and vpiRegBit,
// vpiArrayVar and vpiRegArray (§37.17 detail 19) - the clause lets either be
// reported, and the IEEE 1364 spelling Annex K defines is.
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

// The spelling of `type`, or null for a value neither annex defines as an
// object type.
static const char* VpiTypeConstantName(int type) {
  return VpiConstantNameIn(kVpiTypeNames, type);
}

// §37.3.2: an operation's vpiOpType is one of the additional type properties;
// its integer value names an operator constant in the vpiOpType return-value
// namespace, Annex K's and the ones Annex M adds, each listed here with its
// spelling so vpi_get_str(vpiOpType, ...) can hand the name back. Listing
// Annex K's alone left a cast, an `inside` or a wildcard equality nameless.
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

// §37.3.2 with Annex K: the primitive, delay and timing check constants
// vpiPrimType, vpiDelayType and vpiTchkType report, each with its spelling.
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
      return nullptr;
  }
}

// §37.41 detail 10 / §37.15 / §37.30 / §37.36: resolves vpiDefName, whose value
// depends on the object kind - a module/UDP defn reports its own name, a ref
// obj reports its actual interface/modport name, an interface typespec reports
// its modport/interface identifier, and any other kind has no definition name.
static const char* VpiDefNameStr(VpiHandle obj) {
  // §38.11: an instance reports what it is an instance of, which the design
  // recorded against its path; a module object standing for a definition rather
  // than an instance has no such record and its own name is its definition
  // name. An interface or program instance is an instance as a module's is
  // (§37.6, §37.9).
  if (obj->type == kVpiModule || obj->type == vpiInterface ||
      obj->type == vpiProgram) {
    return obj->def_name.empty() ? obj->name.data() : obj->def_name.c_str();
  }
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
  if (VpiIsAtomicStmtObject(obj)) {
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

// §37.83 and §37.10: vpiDefFile is drawn on the attribute object and on an
// instance; one with no recorded definition file - and any other object kind -
// yields null.
static const char* VpiDefFileStr(VpiHandle obj) {
  if (obj->type != vpiAttribute && !VpiIsInstanceType(obj->type)) {
    return nullptr;
  }
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

// §37.59 detail 2 and §37.42 detail 9: vpiDecompile hands back an expression,
// or a system task or function call, functionally equivalent to the one written
// in the source. It is drawn on the expressions and the system task calls; any
// other object kind, and one that stored no decompiled form, yields null rather
// than an empty string.
static const char* VpiDecompileStr(VpiHandle obj) {
  if (!VpiIsExprType(obj->type) && obj->type != vpiSysTaskCall) return nullptr;
  return obj->decompile.empty() ? nullptr : obj->decompile.c_str();
}

// §38.31 and §38.9: the four callback reasons an application may read the
// save/restart location from. Both clauses name two of them and neither names
// any other, so a routine running for something else -- or for no callback at
// all -- is not one of the application callback routines they describe.
static bool VpiSaveRestartReasonAllowsLocation(int reason) {
  return reason == kCbStartOfSave || reason == kCbEndOfSave ||
         reason == kCbStartOfRestart || reason == kCbEndOfRestart;
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
    // §37.59 detail 2 and §37.42 detail 9: an expression, or a system task or
    // function call, decompiles to a functionally equivalent one through the
    // vpiDecompile string property.
    case vpiDecompile:
      return VpiDecompileStr(obj);
    default:
      return nullptr;
  }
}

PLI_BYTE8* VpiContext::GetStr(int property, VpiHandle obj) {
  // §38.11: vpi_get_str() returns string property values. The value is placed
  // in a single temporary buffer reused by every call - so a pointer from an
  // earlier call is overwritten by the next - and that buffer is distinct from
  // value_pools_, the storage for s_vpi_value strings. A null raw result (null
  // or protected object, or a property with no string) yields null, not "".
  const char* raw = GetStrRaw(property, obj);
  if (!raw) return nullptr;
  // Reserve once so repeated assigns of typical-length strings keep writing
  // into the same allocation, leaving an earlier returned pointer valid until
  // the next call overwrites its contents.
  if (get_str_buffer_.capacity() < 256) get_str_buffer_.reserve(256);
  get_str_buffer_.assign(raw);
  // §37.4.2: a string property is of type PLI_BYTE8 *, so what leaves here is a
  // pointer an application can hold in one. The buffer is this context's own,
  // and §38.11 makes it the temporary every call overwrites.
  return get_str_buffer_.data();
}

const char* VpiContext::GetStrRaw(int property, VpiHandle obj) {
  if (!obj) {
    // §38.31: a callback routine called for cbStartOfSave or cbEndOfSave can
    // read the path to the save/restart location with
    // vpi_get_str(vpiSaveRestartLocation, NULL), and §38.9 says the same of the
    // two restart reasons. It is the one string property drawn on no object,
    // and a null handle stopped here before reaching any property at all.
    if (property == vpiSaveRestartLocation &&
        VpiSaveRestartReasonAllowsLocation(current_callback_reason_) &&
        !save_restart_location_.empty()) {
      return save_restart_location_.c_str();
    }
    return nullptr;
  }
  // §37.3.6: a protected object's properties are inaccessible unless otherwise
  // specified, so a string query for one is an error. The vpiType and
  // vpiIsProtected properties are the exception - permitted for all objects -
  // so they fall through; any other property records the error and yields no
  // string.
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
