#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace {

TEST(VpiConstantAndStructSim, ValueFormatConstants) {
  EXPECT_EQ(vpiBinStrVal, 1);
  EXPECT_EQ(vpiOctStrVal, 2);
  EXPECT_EQ(vpiHexStrVal, 3);
  EXPECT_EQ(vpiScalarVal, 4);
  EXPECT_EQ(vpiIntVal, 5);
  EXPECT_EQ(vpiRealVal, 6);
  EXPECT_EQ(vpiStringVal, 7);
}

TEST(VpiConstantAndStructSim, ObjectTypeConstants) {
  EXPECT_EQ(vpiModule, 32);
  EXPECT_EQ(vpiNet, 36);
  EXPECT_EQ(vpiReg, 48);
  EXPECT_EQ(vpiPort, 44);
  EXPECT_EQ(vpiCallback, 107);
}

TEST(VpiConstantAndStructSim, TimeTypeConstants) {
  EXPECT_EQ(vpiSimTime, 1);
  EXPECT_EQ(vpiScaledRealTime, 2);
}

TEST(VpiConstantAndStructSim, CallbackReasonConstants) {
  EXPECT_EQ(cbValueChange, 1);
  EXPECT_EQ(cbReadWriteSynch, 2);
  EXPECT_EQ(cbEndOfSimulation, 3);
}

TEST(VpiConstantAndStructSim, VpiValueDefaultInit) {
  s_vpi_value val = {};
  EXPECT_EQ(val.format, 0);
}

TEST(VpiConstantAndStructSim, VpiCbDataDefaultInit) {
  s_cb_data cb = {};
  EXPECT_EQ(cb.reason, 0);
  EXPECT_EQ(cb.obj, nullptr);
  EXPECT_EQ(cb.time, nullptr);
  EXPECT_EQ(cb.value, nullptr);
  EXPECT_EQ(cb.user_data, nullptr);
}

TEST(VpiConstantAndStructSim, VpiSystfDataDefaultInit) {
  s_vpi_systf_data data = {};
  EXPECT_EQ(data.type, 0);
  EXPECT_EQ(data.tfname, nullptr);
  EXPECT_EQ(data.calltf, nullptr);
  EXPECT_EQ(data.user_data, nullptr);
}

TEST(SvVpiUser, AssertionTypes) {
  EXPECT_EQ(vpiAssert, 686);
  EXPECT_EQ(vpiAssume, 687);
  EXPECT_EQ(vpiCover, 688);
  EXPECT_EQ(vpiRestrict, 901);
  EXPECT_EQ(vpiImmediateAssert, 665);
}

TEST(SvVpiUser, VisibilityConstants) {
  EXPECT_EQ(vpiPublicVis, 1);
  EXPECT_EQ(vpiProtectedVis, 2);
  EXPECT_EQ(vpiLocalVis, 3);
}

TEST(SvVpiUser, AlwaysTypeConstants) {
  EXPECT_EQ(vpiAlwaysComb, 2);
  EXPECT_EQ(vpiAlwaysFF, 3);
  EXPECT_EQ(vpiAlwaysLatch, 4);
}

TEST(VpiConstantAndStructSim, VpiTimeDefaultInit) {
  s_vpi_time time = {};
  EXPECT_EQ(time.type, 0);
  EXPECT_EQ(time.high, 0u);
  EXPECT_EQ(time.low, 0u);
  EXPECT_DOUBLE_EQ(time.real, 0.0);
}

TEST(VpiUserHeader, Constants01) {
  EXPECT_EQ(vpiAlways, 1);
  EXPECT_EQ(vpiAssignStmt, 2);
  EXPECT_EQ(vpiAssignment, 3);
  EXPECT_EQ(vpiBegin, 4);
  EXPECT_EQ(vpiCase, 5);
  EXPECT_EQ(vpiCaseItem, 6);
  EXPECT_EQ(vpiConstant, 7);
  EXPECT_EQ(vpiContAssign, 8);
  EXPECT_EQ(vpiDeassign, 9);
  EXPECT_EQ(vpiDefParam, 10);
  EXPECT_EQ(vpiDelayControl, 11);
  EXPECT_EQ(vpiDisable, 12);
  EXPECT_EQ(vpiEventControl, 13);
  EXPECT_EQ(vpiEventStmt, 14);
  EXPECT_EQ(vpiFor, 15);
  EXPECT_EQ(vpiForce, 16);
  EXPECT_EQ(vpiForever, 17);
  EXPECT_EQ(vpiFork, 18);
  EXPECT_EQ(vpiFuncCall, 19);
  EXPECT_EQ(vpiFunction, 20);
  EXPECT_EQ(vpiGate, 21);
  EXPECT_EQ(vpiIf, 22);
  EXPECT_EQ(vpiIfElse, 23);
  EXPECT_EQ(vpiInitial, 24);
  EXPECT_EQ(vpiIntegerVar, 25);
  EXPECT_EQ(vpiInterModPath, 26);
  EXPECT_EQ(vpiIterator, 27);
  EXPECT_EQ(vpiIODecl, 28);
  EXPECT_EQ(vpiMemory, 29);
  EXPECT_EQ(vpiMemoryWord, 30);
  EXPECT_EQ(vpiModPath, 31);
  EXPECT_EQ(vpiNamedBegin, 33);
  EXPECT_EQ(vpiNamedEvent, 34);
  EXPECT_EQ(vpiNamedFork, 35);
  EXPECT_EQ(vpiNetBit, 37);
  EXPECT_EQ(vpiNullStmt, 38);
  EXPECT_EQ(vpiOperation, 39);
  EXPECT_EQ(vpiParamAssign, 40);
  EXPECT_EQ(vpiPartSelect, 42);
  EXPECT_EQ(vpiPathTerm, 43);
}

TEST(VpiUserHeader, Constants02) {
  EXPECT_EQ(vpiPortBit, 45);
  EXPECT_EQ(vpiPrimTerm, 46);
  EXPECT_EQ(vpiRealVar, 47);
  EXPECT_EQ(vpiRegBit, 49);
  EXPECT_EQ(vpiRelease, 50);
  EXPECT_EQ(vpiRepeat, 51);
  EXPECT_EQ(vpiRepeatControl, 52);
  EXPECT_EQ(vpiSchedEvent, 53);
  EXPECT_EQ(vpiSpecParam, 54);
  EXPECT_EQ(vpiSwitch, 55);
  EXPECT_EQ(vpiSysFuncCall, 56);
  EXPECT_EQ(vpiSysTaskCall, 57);
  EXPECT_EQ(vpiTableEntry, 58);
  EXPECT_EQ(vpiTask, 59);
  EXPECT_EQ(vpiTaskCall, 60);
  EXPECT_EQ(vpiTchk, 61);
  EXPECT_EQ(vpiTchkTerm, 62);
  EXPECT_EQ(vpiTimeVar, 63);
  EXPECT_EQ(vpiTimeQueue, 64);
  EXPECT_EQ(vpiUdp, 65);
  EXPECT_EQ(vpiUdpDefn, 66);
  EXPECT_EQ(vpiUserSystf, 67);
  EXPECT_EQ(vpiVarSelect, 68);
  EXPECT_EQ(vpiWait, 69);
  EXPECT_EQ(vpiWhile, 70);
  EXPECT_EQ(vpiAttribute, 105);
  EXPECT_EQ(vpiBitSelect, 106);
  EXPECT_EQ(vpiDelayTerm, 108);
  EXPECT_EQ(vpiDelayDevice, 109);
  EXPECT_EQ(vpiFrame, 110);
  EXPECT_EQ(vpiGateArray, 111);
  EXPECT_EQ(vpiModuleArray, 112);
  EXPECT_EQ(vpiPrimitiveArray, 113);
  EXPECT_EQ(vpiNetArray, 114);
  EXPECT_EQ(vpiRange, 115);
  EXPECT_EQ(vpiRegArray, 116);
  EXPECT_EQ(vpiSwitchArray, 117);
  EXPECT_EQ(vpiUdpArray, 118);
  EXPECT_EQ(vpiContAssignBit, 128);
  EXPECT_EQ(vpiNamedEventArray, 129);
}

TEST(VpiUserHeader, Constants03) {
  EXPECT_EQ(vpiIndexedPartSelect, 130);
  EXPECT_EQ(vpiGenScopeArray, 133);
  EXPECT_EQ(vpiGenScope, 134);
  EXPECT_EQ(vpiGenVar, 135);
  EXPECT_EQ(vpiCondition, 71);
  EXPECT_EQ(vpiDelay, 72);
  EXPECT_EQ(vpiElseStmt, 73);
  EXPECT_EQ(vpiForIncStmt, 74);
  EXPECT_EQ(vpiForInitStmt, 75);
  EXPECT_EQ(vpiHighConn, 76);
  EXPECT_EQ(vpiLhs, 77);
  EXPECT_EQ(vpiIndex, 78);
  EXPECT_EQ(vpiLeftRange, 79);
  EXPECT_EQ(vpiLowConn, 80);
  EXPECT_EQ(vpiParent, 81);
  EXPECT_EQ(vpiRhs, 82);
  EXPECT_EQ(vpiRightRange, 83);
  EXPECT_EQ(vpiScope, 84);
  EXPECT_EQ(vpiSysTfCall, 85);
  EXPECT_EQ(vpiTchkDataTerm, 86);
  EXPECT_EQ(vpiTchkNotifier, 87);
  EXPECT_EQ(vpiTchkRefTerm, 88);
  EXPECT_EQ(vpiArgument, 89);
  EXPECT_EQ(vpiBit, 90);
  EXPECT_EQ(vpiDriver, 91);
  EXPECT_EQ(vpiInternalScope, 92);
  EXPECT_EQ(vpiLoad, 93);
  EXPECT_EQ(vpiModDataPathIn, 94);
  EXPECT_EQ(vpiModPathIn, 95);
  EXPECT_EQ(vpiModPathOut, 96);
  EXPECT_EQ(vpiOperand, 97);
  EXPECT_EQ(vpiPortInst, 98);
  EXPECT_EQ(vpiProcess, 99);
  EXPECT_EQ(vpiVariables, 100);
  EXPECT_EQ(vpiUse, 101);
  EXPECT_EQ(vpiExpr, 102);
  EXPECT_EQ(vpiPrimitive, 103);
  EXPECT_EQ(vpiStmt, 104);
  EXPECT_EQ(vpiActiveTimeFormat, 119);
  EXPECT_EQ(vpiInTerm, 120);
}

TEST(VpiUserHeader, Constants04) {
  EXPECT_EQ(vpiInstanceArray, 121);
  EXPECT_EQ(vpiLocalDriver, 122);
  EXPECT_EQ(vpiLocalLoad, 123);
  EXPECT_EQ(vpiOutTerm, 124);
  EXPECT_EQ(vpiPorts, 125);
  EXPECT_EQ(vpiSimNet, 126);
  EXPECT_EQ(vpiTaskFunc, 127);
  EXPECT_EQ(vpiBaseExpr, 131);
  EXPECT_EQ(vpiWidthExpr, 132);
  EXPECT_EQ(vpiAutomatics, 136);
  EXPECT_EQ(vpiUndefined, -1);
  EXPECT_EQ(vpiFile, 5);
  EXPECT_EQ(vpiLineNo, 6);
  EXPECT_EQ(vpiTopModule, 7);
  EXPECT_EQ(vpiCellInstance, 8);
  EXPECT_EQ(vpiProtected, 10);
  EXPECT_EQ(vpiTimeUnit, 11);
  EXPECT_EQ(vpiTimePrecision, 12);
  EXPECT_EQ(vpiDefNetType, 13);
  EXPECT_EQ(vpiUnconnDrive, 14);
  EXPECT_EQ(vpiHighZ, 1);
  EXPECT_EQ(vpiPull1, 2);
  EXPECT_EQ(vpiPull0, 3);
  EXPECT_EQ(vpiDefFile, 15);
  EXPECT_EQ(vpiDefLineNo, 16);
  EXPECT_EQ(vpiDefDelayMode, 47);
  EXPECT_EQ(vpiDelayModeNone, 1);
  EXPECT_EQ(vpiDelayModePath, 2);
  EXPECT_EQ(vpiDelayModeDistrib, 3);
  EXPECT_EQ(vpiDelayModeUnit, 4);
  EXPECT_EQ(vpiDelayModeZero, 5);
  EXPECT_EQ(vpiDelayModeMTM, 6);
  EXPECT_EQ(vpiDefDecayTime, 48);
  EXPECT_EQ(vpiScalar, 17);
  EXPECT_EQ(vpiVector, 18);
  EXPECT_EQ(vpiExplicitName, 19);
  EXPECT_EQ(vpiMixedIO, 4);
  EXPECT_EQ(vpiNoDirection, 5);
  EXPECT_EQ(vpiConnByName, 21);
  EXPECT_EQ(vpiNetType, 22);
}

TEST(VpiUserHeader, Constants05) {
  EXPECT_EQ(vpiWire, 1);
  EXPECT_EQ(vpiWand, 2);
  EXPECT_EQ(vpiWor, 3);
  EXPECT_EQ(vpiTri, 4);
  EXPECT_EQ(vpiTri0, 5);
  EXPECT_EQ(vpiTri1, 6);
  EXPECT_EQ(vpiTriReg, 7);
  EXPECT_EQ(vpiTriAnd, 8);
  EXPECT_EQ(vpiTriOr, 9);
  EXPECT_EQ(vpiSupply1, 10);
  EXPECT_EQ(vpiSupply0, 11);
  EXPECT_EQ(vpiNone, 12);
  EXPECT_EQ(vpiUwire, 13);
  EXPECT_EQ(vpiNettypeNet, 14);
  EXPECT_EQ(vpiNettypeNetSelect, 15);
  EXPECT_EQ(vpiInterconnect, 16);
  EXPECT_EQ(vpiExplicitScalared, 23);
  EXPECT_EQ(vpiExplicitVectored, 24);
  EXPECT_EQ(vpiExpanded, 25);
  EXPECT_EQ(vpiImplicitDecl, 26);
  EXPECT_EQ(vpiChargeStrength, 27);
  EXPECT_EQ(vpiArray, 28);
  EXPECT_EQ(vpiPortIndex, 29);
  EXPECT_EQ(vpiTermIndex, 30);
  EXPECT_EQ(vpiStrength0, 31);
  EXPECT_EQ(vpiStrength1, 32);
  EXPECT_EQ(vpiPrimType, 33);
  EXPECT_EQ(vpiAndPrim, 1);
  EXPECT_EQ(vpiNandPrim, 2);
  EXPECT_EQ(vpiNorPrim, 3);
  EXPECT_EQ(vpiOrPrim, 4);
  EXPECT_EQ(vpiXorPrim, 5);
  EXPECT_EQ(vpiXnorPrim, 6);
  EXPECT_EQ(vpiBufPrim, 7);
  EXPECT_EQ(vpiNotPrim, 8);
  EXPECT_EQ(vpiBufif0Prim, 9);
  EXPECT_EQ(vpiBufif1Prim, 10);
  EXPECT_EQ(vpiNotif0Prim, 11);
  EXPECT_EQ(vpiNotif1Prim, 12);
  EXPECT_EQ(vpiNmosPrim, 13);
}

TEST(VpiUserHeader, Constants06) {
  EXPECT_EQ(vpiPmosPrim, 14);
  EXPECT_EQ(vpiCmosPrim, 15);
  EXPECT_EQ(vpiRnmosPrim, 16);
  EXPECT_EQ(vpiRpmosPrim, 17);
  EXPECT_EQ(vpiRcmosPrim, 18);
  EXPECT_EQ(vpiRtranPrim, 19);
  EXPECT_EQ(vpiRtranif0Prim, 20);
  EXPECT_EQ(vpiRtranif1Prim, 21);
  EXPECT_EQ(vpiTranPrim, 22);
  EXPECT_EQ(vpiTranif0Prim, 23);
  EXPECT_EQ(vpiTranif1Prim, 24);
  EXPECT_EQ(vpiPullupPrim, 25);
  EXPECT_EQ(vpiPulldownPrim, 26);
  EXPECT_EQ(vpiSeqPrim, 27);
  EXPECT_EQ(vpiCombPrim, 28);
  EXPECT_EQ(vpiPolarity, 34);
  EXPECT_EQ(vpiDataPolarity, 35);
  EXPECT_EQ(vpiPositive, 1);
  EXPECT_EQ(vpiNegative, 2);
  EXPECT_EQ(vpiUnknown, 3);
  EXPECT_EQ(vpiEdge, 36);
  EXPECT_EQ(vpiNoEdge, 0);
  EXPECT_EQ(vpiEdge01, 1);
  EXPECT_EQ(vpiEdge10, 2);
  EXPECT_EQ(vpiEdge0x, 4);
  EXPECT_EQ(vpiEdgex1, 8);
  EXPECT_EQ(vpiEdge1x, 16);
  EXPECT_EQ(vpiEdgex0, 32);
  EXPECT_EQ(vpiPosedge, 13);
  EXPECT_EQ(vpiNegedge, 50);
  EXPECT_EQ(vpiAnyEdge, 63);
  EXPECT_EQ(vpiPathType, 37);
  EXPECT_EQ(vpiPathFull, 1);
  EXPECT_EQ(vpiPathParallel, 2);
  EXPECT_EQ(vpiTchkType, 38);
  EXPECT_EQ(vpiSetup, 1);
  EXPECT_EQ(vpiHold, 2);
  EXPECT_EQ(vpiPeriod, 3);
  EXPECT_EQ(vpiWidth, 4);
  EXPECT_EQ(vpiSkew, 5);
}

TEST(VpiUserHeader, Constants07) {
  EXPECT_EQ(vpiRecovery, 6);
  EXPECT_EQ(vpiNoChange, 7);
  EXPECT_EQ(vpiSetupHold, 8);
  EXPECT_EQ(vpiFullskew, 9);
  EXPECT_EQ(vpiRecrem, 10);
  EXPECT_EQ(vpiRemoval, 11);
  EXPECT_EQ(vpiTimeskew, 12);
  EXPECT_EQ(vpiOpType, 39);
  EXPECT_EQ(vpiMinusOp, 1);
  EXPECT_EQ(vpiPlusOp, 2);
  EXPECT_EQ(vpiNotOp, 3);
  EXPECT_EQ(vpiBitNegOp, 4);
  EXPECT_EQ(vpiUnaryAndOp, 5);
  EXPECT_EQ(vpiUnaryNandOp, 6);
  EXPECT_EQ(vpiUnaryOrOp, 7);
  EXPECT_EQ(vpiUnaryNorOp, 8);
  EXPECT_EQ(vpiUnaryXorOp, 9);
  EXPECT_EQ(vpiUnaryXNorOp, 10);
  EXPECT_EQ(vpiSubOp, 11);
  EXPECT_EQ(vpiDivOp, 12);
  EXPECT_EQ(vpiModOp, 13);
  EXPECT_EQ(vpiEqOp, 14);
  EXPECT_EQ(vpiNeqOp, 15);
  EXPECT_EQ(vpiCaseEqOp, 16);
  EXPECT_EQ(vpiCaseNeqOp, 17);
  EXPECT_EQ(vpiGtOp, 18);
  EXPECT_EQ(vpiGeOp, 19);
  EXPECT_EQ(vpiLtOp, 20);
  EXPECT_EQ(vpiLeOp, 21);
  EXPECT_EQ(vpiLShiftOp, 22);
  EXPECT_EQ(vpiRShiftOp, 23);
  EXPECT_EQ(vpiAddOp, 24);
  EXPECT_EQ(vpiMultOp, 25);
  EXPECT_EQ(vpiLogAndOp, 26);
  EXPECT_EQ(vpiLogOrOp, 27);
  EXPECT_EQ(vpiBitAndOp, 28);
  EXPECT_EQ(vpiBitOrOp, 29);
  EXPECT_EQ(vpiBitXorOp, 30);
  EXPECT_EQ(vpiBitXNorOp, 31);
  EXPECT_EQ(vpiBitXnorOp, 31);
}

TEST(VpiUserHeader, Constants08) {
  EXPECT_EQ(vpiConditionOp, 32);
  EXPECT_EQ(vpiConcatOp, 33);
  EXPECT_EQ(vpiMultiConcatOp, 34);
  EXPECT_EQ(vpiEventOrOp, 35);
  EXPECT_EQ(vpiNullOp, 36);
  EXPECT_EQ(vpiListOp, 37);
  EXPECT_EQ(vpiMinTypMaxOp, 38);
  EXPECT_EQ(vpiPosedgeOp, 39);
  EXPECT_EQ(vpiNegedgeOp, 40);
  EXPECT_EQ(vpiArithLShiftOp, 41);
  EXPECT_EQ(vpiArithRShiftOp, 42);
  EXPECT_EQ(vpiPowerOp, 43);
  EXPECT_EQ(vpiConstType, 40);
  EXPECT_EQ(vpiDecConst, 1);
  EXPECT_EQ(vpiRealConst, 2);
  EXPECT_EQ(vpiBinaryConst, 3);
  EXPECT_EQ(vpiOctConst, 4);
  EXPECT_EQ(vpiHexConst, 5);
  EXPECT_EQ(vpiStringConst, 6);
  EXPECT_EQ(vpiIntConst, 7);
  EXPECT_EQ(vpiTimeConst, 8);
  EXPECT_EQ(vpiBlocking, 41);
  EXPECT_EQ(vpiCaseType, 42);
  EXPECT_EQ(vpiCaseExact, 1);
  EXPECT_EQ(vpiCaseX, 2);
  EXPECT_EQ(vpiCaseZ, 3);
  EXPECT_EQ(vpiNetDeclAssign, 43);
  EXPECT_EQ(vpiFuncType, 44);
  EXPECT_EQ(vpiIntFunc, 1);
  EXPECT_EQ(vpiRealFunc, 2);
  EXPECT_EQ(vpiTimeFunc, 3);
  EXPECT_EQ(vpiSizedFunc, 4);
  EXPECT_EQ(vpiSizedSignedFunc, 5);
  EXPECT_EQ(vpiSysFuncType, 44);
  EXPECT_EQ(vpiSysFuncInt, 1);
  EXPECT_EQ(vpiSysFuncReal, 2);
  EXPECT_EQ(vpiSysFuncTime, 3);
  EXPECT_EQ(vpiSysFuncSized, 4);
  EXPECT_EQ(vpiUserDefn, 45);
  EXPECT_EQ(vpiScheduled, 46);
}

TEST(VpiUserHeader, Constants09) {
  EXPECT_EQ(vpiActive, 49);
  EXPECT_EQ(vpiAutomatic, 50);
  EXPECT_EQ(vpiConstantSelect, 53);
  EXPECT_EQ(vpiDecompile, 54);
  EXPECT_EQ(vpiDefAttribute, 55);
  EXPECT_EQ(vpiDelayType, 56);
  EXPECT_EQ(vpiModPathDelay, 1);
  EXPECT_EQ(vpiInterModPathDelay, 2);
  EXPECT_EQ(vpiMIPDelay, 3);
  EXPECT_EQ(vpiIteratorType, 57);
  EXPECT_EQ(vpiOffset, 60);
  EXPECT_EQ(vpiResolvedNetType, 61);
  EXPECT_EQ(vpiSaveRestartID, 62);
  EXPECT_EQ(vpiSaveRestartLocation, 63);
  EXPECT_EQ(vpiValid, 64);
  EXPECT_EQ(vpiValidFalse, 0);
  EXPECT_EQ(vpiValidTrue, 1);
  EXPECT_EQ(vpiSigned, 65);
  EXPECT_EQ(vpiLocalParam, 70);
  EXPECT_EQ(vpiModPathHasIfNone, 71);
  EXPECT_EQ(vpiIndexedPartSelectType, 72);
  EXPECT_EQ(vpiPosIndexed, 1);
  EXPECT_EQ(vpiNegIndexed, 2);
  EXPECT_EQ(vpiIsMemory, 73);
  EXPECT_EQ(vpiIsProtected, 74);
  EXPECT_EQ(vpiSetInteractiveScope, 69);
  EXPECT_EQ(VPI_MCD_STDOUT, 1);
  EXPECT_EQ(vpiSuppressTime, 3);
  EXPECT_EQ(vpiSupplyDrive, 128);
  EXPECT_EQ(vpiStrongDrive, 64);
  EXPECT_EQ(vpiPullDrive, 32);
  EXPECT_EQ(vpiWeakDrive, 8);
  EXPECT_EQ(vpiLargeCharge, 16);
  EXPECT_EQ(vpiMediumCharge, 4);
  EXPECT_EQ(vpiSmallCharge, 2);
  EXPECT_EQ(vpiHiZ, 1);
  EXPECT_EQ(vpiDecStrVal, 3);
  EXPECT_EQ(vpiStrengthVal, 10);
  EXPECT_EQ(vpiObjTypeVal, 12);
  EXPECT_EQ(vpiSuppressVal, 13);
}

TEST(VpiUserHeader, Constants10) {
  EXPECT_EQ(vpiShortIntVal, 14);
  EXPECT_EQ(vpiLongIntVal, 15);
  EXPECT_EQ(vpiShortRealVal, 16);
  EXPECT_EQ(vpiRawTwoStateVal, 17);
  EXPECT_EQ(vpiRawFourStateVal, 18);
  EXPECT_EQ(vpiForceFlag, 5);
  EXPECT_EQ(vpiReleaseFlag, 6);
  EXPECT_EQ(vpiCancelEvent, 7);
  EXPECT_EQ(vpiReturnEvent, 4096);
  EXPECT_EQ(vpiUserAllocFlag, 8192);
  EXPECT_EQ(vpiOneValue, 16384);
  EXPECT_EQ(vpiPropagateOff, 32768);
  EXPECT_EQ(vpiH, 4);
  EXPECT_EQ(vpiL, 5);
  EXPECT_EQ(vpiDontCare, 6);
  EXPECT_EQ(vpiCompile, 1);
  EXPECT_EQ(vpiPLI, 2);
  EXPECT_EQ(vpiRun, 3);
  EXPECT_EQ(vpiSystem, 4);
  EXPECT_EQ(cbForce, 3);
  EXPECT_EQ(cbRelease, 4);
  EXPECT_EQ(cbAssign, 25);
  EXPECT_EQ(cbDeassign, 26);
  EXPECT_EQ(cbDisable, 27);
}

TEST(VpiUserHeader, PortabilityTypedefWidths) {
  EXPECT_EQ(sizeof(PLI_INT32), 4u);
  EXPECT_EQ(sizeof(PLI_UINT32), 4u);
  EXPECT_EQ(sizeof(PLI_INT64), 8u);
  EXPECT_EQ(sizeof(PLI_UINT64), 8u);
  EXPECT_EQ(sizeof(PLI_INT16), 2u);
  EXPECT_EQ(sizeof(PLI_UINT16), 2u);
  EXPECT_EQ(sizeof(PLI_BYTE8), 1u);
  EXPECT_EQ(sizeof(PLI_UBYTE8), 1u);
  EXPECT_TRUE(static_cast<PLI_INT32>(-1) < 0);
  EXPECT_TRUE(static_cast<PLI_UINT32>(-1) > 0);
}

TEST(VpiUserHeader, VpiDelayDefaultInit) {
  s_vpi_delay d = {};
  EXPECT_EQ(d.da, nullptr);
  EXPECT_EQ(d.no_of_delays, 0);
  EXPECT_EQ(d.time_type, 0);
  EXPECT_EQ(d.mtm_flag, 0);
  EXPECT_EQ(d.append_flag, 0);
  EXPECT_EQ(d.pulsere_flag, 0);
}

TEST(VpiUserHeader, VpiStrengthValDefaultInit) {
  s_vpi_strengthval s = {};
  EXPECT_EQ(s.logic, 0);
  EXPECT_EQ(s.s0, 0);
  EXPECT_EQ(s.s1, 0);
}

TEST(VpiUserHeader, VpiArrayValueDefaultInit) {
  s_vpi_arrayvalue a = {};
  EXPECT_EQ(a.format, 0u);
  EXPECT_EQ(a.flags, 0u);
  EXPECT_EQ(a.value.integers, nullptr);
}

TEST(VpiUserHeader, VpiArrayValueUnionArmsAreAddressable) {
  // §K.2: the array value's union carries one arm per element encoding. Each
  // arm is observed by aiming it at storage of the matching element type and
  // reading the value back through the same arm of the production struct.
  PLI_INT32 ints[2] = {7, 9};
  PLI_INT16 shorts[2] = {1, 2};
  PLI_INT64 longs[2] = {1, 2};
  PLI_BYTE8 raw[2] = {'a', 'b'};
  double reals[2] = {1.5, 2.5};
  float shortreals[2] = {0.5f, 0.25f};
  s_vpi_vecval vecs[1] = {};
  s_vpi_time times[1] = {};

  s_vpi_arrayvalue a = {};
  a.format = vpiShortIntVal;
  a.flags = vpiUserAllocFlag;
  EXPECT_EQ(a.format, vpiShortIntVal);
  EXPECT_EQ(a.flags, static_cast<unsigned>(vpiUserAllocFlag));

  a.value.integers = ints;
  EXPECT_EQ(a.value.integers[1], 9);
  a.value.shortints = shorts;
  EXPECT_EQ(a.value.shortints[0], 1);
  a.value.longints = longs;
  EXPECT_EQ(a.value.longints[1], 2);
  a.value.rawvals = raw;
  EXPECT_EQ(a.value.rawvals[0], 'a');
  a.value.reals = reals;
  EXPECT_DOUBLE_EQ(a.value.reals[0], 1.5);
  a.value.shortreals = shortreals;
  EXPECT_FLOAT_EQ(a.value.shortreals[1], 0.25f);
  a.value.vectors = vecs;
  EXPECT_EQ(a.value.vectors, vecs);
  a.value.times = times;
  EXPECT_EQ(a.value.times, times);
}

TEST(VpiUserHeader, VpiDelayHoldsDelayArrayAndFlags) {
  // §K.2: the delay structure points at an application-allocated array of time
  // values and carries the mtm/append/pulse-reject flags. Populate it and read
  // back through the production struct, including the suppress-time code.
  s_vpi_time slots[2] = {};
  slots[0].low = 5u;
  slots[1].low = 11u;

  s_vpi_delay d = {};
  d.da = slots;
  d.no_of_delays = 2;
  d.time_type = vpiSuppressTime;
  d.mtm_flag = 1;
  d.append_flag = 1;
  d.pulsere_flag = 1;

  EXPECT_EQ(d.da[1].low, 11u);
  EXPECT_EQ(d.no_of_delays, 2);
  EXPECT_EQ(d.time_type, vpiSuppressTime);
  EXPECT_EQ(d.mtm_flag, 1);
  EXPECT_EQ(d.append_flag, 1);
  EXPECT_EQ(d.pulsere_flag, 1);
}

TEST(VpiUserHeader, VpiStrengthValHoldsStrengthCoding) {
  // §K.2: the scalar strength value pairs a logic code with two components
  // drawn from the strength masks.
  s_vpi_strengthval s = {};
  s.logic = vpi1;
  s.s0 = vpiSupplyDrive;
  s.s1 = vpiWeakDrive;
  EXPECT_EQ(s.logic, vpi1);
  EXPECT_EQ(s.s0, 0x80);
  EXPECT_EQ(s.s1, 0x08);
}

TEST(VpiUserHeader, PortabilityTypedefValueRanges) {
  // §K.2 sizes the PLI integer types so the wide variants carry values past the
  // 32-bit range and the signed variants represent negatives.
  PLI_INT64 wide = 5000000000;  // beyond 2^32
  EXPECT_GT(wide, static_cast<PLI_INT64>(0xFFFFFFFF));
  PLI_UINT64 uwide = 0xFFFFFFFFFFULL;  // 40-bit value
  EXPECT_EQ(uwide >> 32, 0xFFULL);
  PLI_INT16 neg = -12345;
  EXPECT_LT(neg, 0);
  PLI_UINT16 big16 = 0xFFFF;
  EXPECT_EQ(big16, 65535);
}

TEST(VpiUserHeader, AliasConstantsMatchCanonical) {
  // §K.2 defines several constants as aliases of an earlier name; each alias
  // resolves to the same value as its canonical macro.
  EXPECT_EQ(vpiBitXnorOp, vpiBitXNorOp);
  EXPECT_EQ(vpiSysFuncType, vpiFuncType);
  EXPECT_EQ(vpiSysFuncInt, vpiIntFunc);
  EXPECT_EQ(vpiSysFuncReal, vpiRealFunc);
  EXPECT_EQ(vpiSysFuncTime, vpiTimeFunc);
  EXPECT_EQ(vpiSysFuncSized, vpiSizedFunc);
}

TEST(VpiUserHeader, EdgeBitsComposeIntoPosNegAnyEdge) {
  // §K.2 builds the posedge/negedge/anyedge masks from the single-bit edge
  // transitions; vpiNoEdge is the empty mask and the six transitions are
  // mutually exclusive single bits.
  EXPECT_EQ(vpiNoEdge, 0);
  EXPECT_EQ(vpiPosedge, vpiEdgex1 | vpiEdge01 | vpiEdge0x);
  EXPECT_EQ(vpiNegedge, vpiEdgex0 | vpiEdge10 | vpiEdge1x);
  EXPECT_EQ(vpiAnyEdge, vpiPosedge | vpiNegedge);
  int all =
      vpiEdge01 | vpiEdge10 | vpiEdge0x | vpiEdgex1 | vpiEdge1x | vpiEdgex0;
  EXPECT_EQ(all, 0x3F);
}

TEST(VpiUserHeader, ValueRoutineFlagBitsDoNotOverlap) {
  // §K.2 reserves a distinct bit for each put/get value flag so they may be
  // combined without collision.
  EXPECT_EQ(vpiReturnEvent & vpiUserAllocFlag, 0);
  EXPECT_EQ(vpiReturnEvent & vpiOneValue, 0);
  EXPECT_EQ(vpiUserAllocFlag & vpiPropagateOff, 0);
  EXPECT_EQ(vpiOneValue & vpiPropagateOff, 0);
  int combined =
      vpiReturnEvent | vpiUserAllocFlag | vpiOneValue | vpiPropagateOff;
  EXPECT_EQ(combined, 0xF000);
}

TEST(VpiUserHeader, StrengthMasksOccupyDistinctBits) {
  // §K.2 gives each drive and charge strength its own bit; ORing all eight
  // yields a full byte, confirming none overlap.
  int all = vpiSupplyDrive | vpiStrongDrive | vpiPullDrive | vpiLargeCharge |
            vpiWeakDrive | vpiMediumCharge | vpiSmallCharge | vpiHiZ;
  EXPECT_EQ(all, 0xFF);
  EXPECT_EQ(vpiSupplyDrive & vpiStrongDrive, 0);
}

}  // namespace
