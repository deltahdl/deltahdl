#pragma once

#include <cstdarg>
#include <cstdint>

#include "simulator/vpi_context.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_pli_types.h"

using vpiHandle = delta::VpiHandle;
using s_vpi_value = delta::VpiValue;
using s_vpi_time = delta::VpiTime;
using s_cb_data = delta::VpiCbData;
using s_vpi_systf_data = delta::VpiSystfData;
using s_vpi_vecval = delta::VpiVectorVal;
using SVpiErrorInfo = delta::VpiErrorInfo;
using SVpiVlogInfo = delta::VpiVlogInfo;

#define vpiModule 32
#define vpiNet 36
#define vpiReg 48
#define vpiPort 44
#define vpiParameter 41
#define vpiCallback 107

#define vpiBinStrVal 1
#define vpiOctStrVal 2
#define vpiHexStrVal 3
#define vpiScalarVal 4
#define vpiIntVal 5
#define vpiRealVal 6
#define vpiStringVal 7
#define vpiTimeVal 8
#define vpiVectorVal 9

#define vpiSimTime 1
#define vpiScaledRealTime 2

#define cbValueChange 1
#define cbReadWriteSynch 2
#define cbEndOfSimulation 3
#define cbStmt 4
#define cbAtStartOfSimTime 5
#define cbReadOnlySynch 6
#define cbAfterDelay 7
#define cbNextSimTime 8
#define cbNBASynch 9
#define cbAtEndOfSimTime 10

// §38.36.3 simulator action/feature callback reasons (mirror of the kCb*
// values).
#define cbEndOfCompile 11
#define cbStartOfSimulation 12
#define cbError 13
#define cbPLIError 14
#define cbTchkViolation 15
#define cbSignal 16
#define cbStartOfSave 17
#define cbEndOfSave 18
#define cbStartOfRestart 19
#define cbEndOfRestart 20
#define cbStartOfReset 21
#define cbEndOfReset 22
#define cbEnterInteractive 23
#define cbExitInteractive 24
#define cbInteractiveScopeChange 25
#define cbUnresolvedSystf 26

#define vpiType 1
#define vpiName 2
#define vpiFullName 3
#define vpiSize 4
#define vpiDirection 5
#define vpiDefName 6
#define vpiLibrary 67
#define vpiConfig 70
#define vpiCell 71

#define vpiInput 1
#define vpiOutput 2
#define vpiInout 3

#define vpiNoDelay 1
#define vpiInertialDelay 2
#define vpiTransportDelay 3
#define vpiPureTransportDelay 4

#define vpiFinish 66
#define vpiStop 67
#define vpiReset 68

#define vpi0 0
#define vpi1 1
#define vpiX 2
#define vpiZ 3

// §38.2 Table 38-1: vpi_chk_error() severity levels, lowest to highest.
#define vpiNotice 1
#define vpiWarning 2
#define vpiError 3
#define vpiSystem 4
#define vpiInternal 5

#define vpiSysTask 1
#define vpiSysFunc 2

// ----------------------------------------------------------------------------
// §K.2 (Annex K, normative): vpi_user.h source code. The constants, sized
// portability typedefs and value/delay/strength structures below complete
// the include file that every SystemVerilog simulator is required to
// provide. Symbols already supplied by other clauses (object kinds,
// callback reasons, control codes, value formats, etc.) are not repeated.
// ----------------------------------------------------------------------------
// §K.2: the vpi_user.h portability layer fixes the width of the integer types
// every VPI routine and structure is expressed in. The PLI_* aliases now live
// in vpi_pli_types.h (included above) so headers pulled in earlier can see
// them.

#define vpiAlways 1
#define vpiAssignStmt 2
#define vpiAssignment 3
#define vpiBegin 4
#define vpiCase 5
#define vpiCaseItem 6
#define vpiConstant 7
#define vpiContAssign 8
#define vpiDeassign 9
#define vpiDefParam 10
#define vpiDelayControl 11
#define vpiDisable 12
#define vpiEventControl 13
#define vpiEventStmt 14
#define vpiFor 15
#define vpiForce 16
#define vpiForever 17
#define vpiFork 18
#define vpiFuncCall 19
#define vpiFunction 20
#define vpiGate 21
#define vpiIf 22
#define vpiIfElse 23
#define vpiInitial 24
#define vpiIntegerVar 25
#define vpiInterModPath 26
#define vpiIterator 27
#define vpiIODecl 28
#define vpiMemory 29
#define vpiMemoryWord 30
#define vpiModPath 31
#define vpiNamedBegin 33
#define vpiNamedEvent 34
#define vpiNamedFork 35
#define vpiNetBit 37
#define vpiNullStmt 38
#define vpiOperation 39
#define vpiParamAssign 40
#define vpiPartSelect 42
#define vpiPathTerm 43
#define vpiPortBit 45
#define vpiPrimTerm 46
#define vpiRealVar 47
#define vpiRegBit 49
#define vpiRelease 50
#define vpiRepeat 51
#define vpiRepeatControl 52
#define vpiSchedEvent 53
#define vpiSpecParam 54
#define vpiSwitch 55
#define vpiSysFuncCall 56
#define vpiSysTaskCall 57
#define vpiTableEntry 58
#define vpiTask 59
#define vpiTaskCall 60
#define vpiTchk 61
#define vpiTchkTerm 62
#define vpiTimeVar 63
#define vpiTimeQueue 64
#define vpiUdp 65
#define vpiUdpDefn 66
#define vpiUserSystf 67
#define vpiVarSelect 68
#define vpiWait 69
#define vpiWhile 70
#define vpiAttribute 105
#define vpiBitSelect 106
#define vpiDelayTerm 108
#define vpiDelayDevice 109
#define vpiFrame 110
#define vpiGateArray 111
#define vpiModuleArray 112
#define vpiPrimitiveArray 113
#define vpiNetArray 114
#define vpiRange 115
#define vpiRegArray 116
#define vpiSwitchArray 117
#define vpiUdpArray 118
#define vpiContAssignBit 128
#define vpiNamedEventArray 129
#define vpiIndexedPartSelect 130
#define vpiGenScopeArray 133
#define vpiGenScope 134
#define vpiGenVar 135
#define vpiCondition 71
#define vpiDelay 72
#define vpiElseStmt 73
#define vpiForIncStmt 74
#define vpiForInitStmt 75
#define vpiHighConn 76
#define vpiLhs 77
#define vpiIndex 78
#define vpiLeftRange 79
#define vpiLowConn 80
#define vpiParent 81
#define vpiRhs 82
#define vpiRightRange 83
#define vpiScope 84
#define vpiSysTfCall 85
#define vpiTchkDataTerm 86
#define vpiTchkNotifier 87
#define vpiTchkRefTerm 88
#define vpiArgument 89
#define vpiBit 90
#define vpiDriver 91
#define vpiInternalScope 92
#define vpiLoad 93
#define vpiModDataPathIn 94
#define vpiModPathIn 95
#define vpiModPathOut 96
#define vpiOperand 97
#define vpiPortInst 98
#define vpiProcess 99
#define vpiVariables 100
#define vpiUse 101
#define vpiExpr 102
#define vpiPrimitive 103
#define vpiStmt 104
#define vpiActiveTimeFormat 119
#define vpiInTerm 120
#define vpiInstanceArray 121
#define vpiLocalDriver 122
#define vpiLocalLoad 123
#define vpiOutTerm 124
#define vpiPorts 125
#define vpiSimNet 126
#define vpiTaskFunc 127
#define vpiBaseExpr 131
#define vpiWidthExpr 132
#define vpiAutomatics 136
#define vpiUndefined -1
#define vpiFile 5
#define vpiLineNo 6
#define vpiTopModule 7
#define vpiCellInstance 8
#define vpiProtected 10
#define vpiTimeUnit 11
#define vpiTimePrecision 12
#define vpiDefNetType 13
#define vpiUnconnDrive 14
#define vpiHighZ 1
#define vpiPull1 2
#define vpiPull0 3
#define vpiDefFile 15
#define vpiDefLineNo 16
#define vpiDefDelayMode 47
#define vpiDelayModeNone 1
#define vpiDelayModePath 2
#define vpiDelayModeDistrib 3
#define vpiDelayModeUnit 4
#define vpiDelayModeZero 5
#define vpiDelayModeMTM 6
#define vpiDefDecayTime 48
#define vpiScalar 17
#define vpiVector 18
#define vpiExplicitName 19
#define vpiMixedIO 4
#define vpiNoDirection 5
#define vpiConnByName 21
#define vpiNetType 22
#define vpiWire 1
#define vpiWand 2
#define vpiWor 3
#define vpiTri 4
#define vpiTri0 5
#define vpiTri1 6
#define vpiTriReg 7
#define vpiTriAnd 8
#define vpiTriOr 9
#define vpiSupply1 10
#define vpiSupply0 11
#define vpiNone 12
#define vpiUwire 13
#define vpiNettypeNet 14
#define vpiNettypeNetSelect 15
#define vpiInterconnect 16
#define vpiExplicitScalared 23
#define vpiExplicitVectored 24
#define vpiExpanded 25
#define vpiImplicitDecl 26
#define vpiChargeStrength 27
#define vpiArray 28
#define vpiPortIndex 29
#define vpiTermIndex 30
#define vpiStrength0 31
#define vpiStrength1 32
#define vpiPrimType 33
#define vpiAndPrim 1
#define vpiNandPrim 2
#define vpiNorPrim 3
#define vpiOrPrim 4
#define vpiXorPrim 5
#define vpiXnorPrim 6
#define vpiBufPrim 7
#define vpiNotPrim 8
#define vpiBufif0Prim 9
#define vpiBufif1Prim 10
#define vpiNotif0Prim 11
#define vpiNotif1Prim 12
#define vpiNmosPrim 13
#define vpiPmosPrim 14
#define vpiCmosPrim 15
#define vpiRnmosPrim 16
#define vpiRpmosPrim 17
#define vpiRcmosPrim 18
#define vpiRtranPrim 19
#define vpiRtranif0Prim 20
#define vpiRtranif1Prim 21
#define vpiTranPrim 22
#define vpiTranif0Prim 23
#define vpiTranif1Prim 24
#define vpiPullupPrim 25
#define vpiPulldownPrim 26
#define vpiSeqPrim 27
#define vpiCombPrim 28
#define vpiPolarity 34
#define vpiDataPolarity 35
#define vpiPositive 1
#define vpiNegative 2
#define vpiUnknown 3
#define vpiEdge 36
#define vpiNoEdge 0x00
#define vpiEdge01 0x01
#define vpiEdge10 0x02
#define vpiEdge0x 0x04
#define vpiEdgex1 0x08
#define vpiEdge1x 0x10
#define vpiEdgex0 0x20
#define vpiPosedge (vpiEdgex1 | vpiEdge01 | vpiEdge0x)
#define vpiNegedge (vpiEdgex0 | vpiEdge10 | vpiEdge1x)
#define vpiAnyEdge (vpiPosedge | vpiNegedge)
#define vpiPathType 37
#define vpiPathFull 1
#define vpiPathParallel 2
#define vpiTchkType 38
#define vpiSetup 1
#define vpiHold 2
#define vpiPeriod 3
#define vpiWidth 4
#define vpiSkew 5
#define vpiRecovery 6
#define vpiNoChange 7
#define vpiSetupHold 8
#define vpiFullskew 9
#define vpiRecrem 10
#define vpiRemoval 11
#define vpiTimeskew 12
#define vpiOpType 39
#define vpiMinusOp 1
#define vpiPlusOp 2
#define vpiNotOp 3
#define vpiBitNegOp 4
#define vpiUnaryAndOp 5
#define vpiUnaryNandOp 6
#define vpiUnaryOrOp 7
#define vpiUnaryNorOp 8
#define vpiUnaryXorOp 9
#define vpiUnaryXNorOp 10
#define vpiSubOp 11
#define vpiDivOp 12
#define vpiModOp 13
#define vpiEqOp 14
#define vpiNeqOp 15
#define vpiCaseEqOp 16
#define vpiCaseNeqOp 17
#define vpiGtOp 18
#define vpiGeOp 19
#define vpiLtOp 20
#define vpiLeOp 21
#define vpiLShiftOp 22
#define vpiRShiftOp 23
#define vpiAddOp 24
#define vpiMultOp 25
#define vpiLogAndOp 26
#define vpiLogOrOp 27
#define vpiBitAndOp 28
#define vpiBitOrOp 29
#define vpiBitXorOp 30
#define vpiBitXNorOp 31
#define vpiBitXnorOp vpiBitXNorOp
#define vpiConditionOp 32
#define vpiConcatOp 33
#define vpiMultiConcatOp 34
#define vpiEventOrOp 35
#define vpiNullOp 36
#define vpiListOp 37
#define vpiMinTypMaxOp 38
#define vpiPosedgeOp 39
#define vpiNegedgeOp 40
#define vpiArithLShiftOp 41
#define vpiArithRShiftOp 42
#define vpiPowerOp 43
#define vpiConstType 40
#define vpiDecConst 1
#define vpiRealConst 2
#define vpiBinaryConst 3
#define vpiOctConst 4
#define vpiHexConst 5
#define vpiStringConst 6
#define vpiIntConst 7
#define vpiTimeConst 8
#define vpiBlocking 41
#define vpiCaseType 42
#define vpiCaseExact 1
#define vpiCaseX 2
#define vpiCaseZ 3
#define vpiNetDeclAssign 43
#define vpiFuncType 44
#define vpiIntFunc 1
#define vpiRealFunc 2
#define vpiTimeFunc 3
#define vpiSizedFunc 4
#define vpiSizedSignedFunc 5
#define vpiSysFuncType vpiFuncType
#define vpiSysFuncInt vpiIntFunc
#define vpiSysFuncReal vpiRealFunc
#define vpiSysFuncTime vpiTimeFunc
#define vpiSysFuncSized vpiSizedFunc
#define vpiUserDefn 45
#define vpiScheduled 46
#define vpiActive 49
#define vpiAutomatic 50

// §37.3.7: allocation-scheme property selector and its three return values. The
// selector (731) is a free property number; the return values share the small
// property-result namespace.
#define vpiAllocScheme 731
#define vpiAutomaticScheme 1
#define vpiDynamicScheme 2
#define vpiOtherScheme 3
#define vpiConstantSelect 53
#define vpiDecompile 54
#define vpiDefAttribute 55
#define vpiDelayType 56
#define vpiModPathDelay 1
#define vpiInterModPathDelay 2
#define vpiMIPDelay 3
#define vpiIteratorType 57
#define vpiOffset 60
#define vpiResolvedNetType 61
#define vpiSaveRestartID 62
#define vpiSaveRestartLocation 63
#define vpiValid 64
#define vpiValidFalse 0
#define vpiValidTrue 1
#define vpiSigned 65
#define vpiLocalParam 70
#define vpiModPathHasIfNone 71
#define vpiIndexedPartSelectType 72
#define vpiPosIndexed 1
#define vpiNegIndexed 2
#define vpiIsMemory 73
#define vpiIsProtected 74
#define vpiSetInteractiveScope 69
#define VPI_MCD_STDOUT 0x00000001
#define vpiSuppressTime 3
#define vpiSupplyDrive 0x80
#define vpiStrongDrive 0x40
#define vpiPullDrive 0x20
#define vpiWeakDrive 0x08
#define vpiLargeCharge 0x10
#define vpiMediumCharge 0x04
#define vpiSmallCharge 0x02
#define vpiHiZ 0x01
#define vpiDecStrVal 3
#define vpiStrengthVal 10
#define vpiObjTypeVal 12
#define vpiSuppressVal 13
#define vpiShortIntVal 14
#define vpiLongIntVal 15
#define vpiShortRealVal 16
#define vpiRawTwoStateVal 17
#define vpiRawFourStateVal 18
#define vpiForceFlag 5
#define vpiReleaseFlag 6
#define vpiCancelEvent 7
#define vpiReturnEvent 0x1000
#define vpiUserAllocFlag 0x2000
#define vpiOneValue 0x4000
#define vpiPropagateOff 0x8000
#define vpiH 4
#define vpiL 5
#define vpiDontCare 6
#define vpiCompile 1
#define vpiPLI 2
#define vpiRun 3
#define cbForce 3
#define cbRelease 4
#define cbAssign 25
#define cbDeassign 26
#define cbDisable 27

// §37.17 Variables / §37.22 Object range: the variable object kinds (vpiBitVar,
// vpiStructVar, ...), the backward-compatibility aliases of detail 19
// (vpiVarBit, vpiLogicVar, vpiArrayVar), and the related properties
// (vpiArrayType, vpiRandType, vpiVisibility, vpiArrayMember,
// vpiStructUnionMember, ...) are all defined by the Annex M source listing in
// sv_vpi_user.h. The range relations (vpiSize, vpiLeftRange, vpiRightRange,
// vpiRange, vpiBit, vpiIndex, vpiParent, vpiScalar, vpiVector,
// vpiConstantSelect, vpiDecompile) are defined above. The helpers declared
// below apply the clause rules on top of those constants.

// §K.2: delay structure exchanged with the delay-processing routines. The
// definition lives inside the delta namespace (VpiDelay) so the simulator's
// implementation can name it directly; these aliases expose it under the
// standard PLI spellings.
using s_vpi_delay = delta::VpiDelay;
using p_vpi_delay = delta::VpiDelay*;

// §K.2: scalar strength value. logic holds a vpi0/vpi1/vpiX/vpiZ code and the
// s0/s1 fields carry the drive/charge strength components.
typedef struct t_vpi_strengthval {
  PLI_INT32 logic = 0;
  PLI_INT32 s0 = 0;
  PLI_INT32 s1 = 0;
} s_vpi_strengthval, *p_vpi_strengthval;

// §K.2: aggregate value used by the array value routines. The format selects
// which arm of the union is live; flags carries vpiUserAllocFlag and friends.
// The definition lives inside the delta namespace (VpiArrayValue) so the
// simulator can name it directly; these aliases expose it under the standard
// PLI spellings.
using s_vpi_arrayvalue = delta::VpiArrayValue;
using p_vpi_arrayvalue = delta::VpiArrayValue*;

vpiHandle vpi_register_systf(s_vpi_systf_data* data);
void vpi_get_systf_info(vpiHandle obj, s_vpi_systf_data* systf_data_p);
void vpi_get_cb_info(vpiHandle obj, s_cb_data* cb_data_p);
void vpi_get_time(vpiHandle obj, s_vpi_time* time_p);
void vpi_get_delays(vpiHandle obj, p_vpi_delay delay_p);
void vpi_put_delays(vpiHandle obj, p_vpi_delay delay_p);
PLI_INT32 vpi_get_data(PLI_INT32 id, PLI_BYTE8* dataLoc, PLI_INT32 numOfBytes);
PLI_INT32 vpi_put_data(PLI_INT32 id, PLI_BYTE8* dataLoc, PLI_INT32 numOfBytes);
PLI_INT32 vpi_put_userdata(vpiHandle obj, void* userdata);
void* vpi_get_userdata(vpiHandle obj);
vpiHandle VpiHandleC(int type, vpiHandle ref);
vpiHandle vpi_handle_by_name(const char* name, vpiHandle scope);
vpiHandle VpiHandleByIndexC(vpiHandle parent, int index);
vpiHandle VpiHandleByMultiIndexC(vpiHandle parent, int num_index,
                                 int* index_array);
vpiHandle VpiHandleMultiC(int type, vpiHandle ref1, vpiHandle ref2);
int VpiCompareObjectsC(vpiHandle obj1, vpiHandle obj2);
vpiHandle vpi_iterate(int type, vpiHandle ref);
vpiHandle vpi_scan(vpiHandle iterator);
void vpi_get_value(vpiHandle obj, s_vpi_value* value);
vpiHandle vpi_put_value(vpiHandle obj, s_vpi_value* value, s_vpi_time* time,
                        int flags);
void vpi_put_value_array(vpiHandle obj, p_vpi_arrayvalue arrayvalue_p,
                         PLI_INT32* index_p, PLI_UINT32 num);
void vpi_get_value_array(vpiHandle obj, p_vpi_arrayvalue arrayvalue_p,
                         PLI_INT32* index_p, PLI_UINT32 num);
vpiHandle vpi_register_cb(s_cb_data* data);
int VpiRemoveCbC(vpiHandle cb_handle);
int vpi_get(int property, vpiHandle obj);
PLI_INT64 vpi_get64(int property, vpiHandle obj);
const char* vpi_get_str(int property, vpiHandle obj);
int vpi_free_object(vpiHandle obj);
PLI_INT32 vpi_release_handle(vpiHandle obj);
int VpiControlC(int operation, ...);
int VpiChkErrorC(SVpiErrorInfo* info);
PLI_INT32 vpi_get_vlog_info(SVpiVlogInfo* info);
PLI_INT32 vpi_flush();
PLI_UINT32 vpi_mcd_open(PLI_BYTE8* file);
PLI_UINT32 vpi_mcd_close(PLI_UINT32 mcd);
PLI_INT32 vpi_mcd_flush(PLI_UINT32 mcd);
PLI_BYTE8* vpi_mcd_name(PLI_UINT32 cd);
PLI_INT32 vpi_mcd_printf(PLI_UINT32 mcd, PLI_BYTE8* format, ...);
PLI_INT32 vpi_mcd_vprintf(PLI_UINT32 mcd, PLI_BYTE8* format, va_list ap);
PLI_INT32 vpi_printf(PLI_BYTE8* format, ...);
PLI_INT32 vpi_vprintf(PLI_BYTE8* format, va_list ap);
