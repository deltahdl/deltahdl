#pragma once

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {

class SimContext;
class Scheduler;
class Arena;
struct Net;
struct Process;
struct Variable;

constexpr int kVpiModule = vpiModule;
constexpr int kVpiNet = vpiNet;
constexpr int kVpiReg = vpiReg;
constexpr int kVpiPort = vpiPort;
constexpr int kVpiParameter = vpiParameter;
constexpr int kVpiCallback = vpiCallback;

constexpr int kVpiTimeQueue = vpiTimeQueue;

constexpr int kVpiBinStrVal = vpiBinStrVal;
constexpr int kVpiDecStrVal = vpiDecStrVal;
constexpr int kVpiOctStrVal = vpiOctStrVal;
constexpr int kVpiHexStrVal = vpiHexStrVal;
constexpr int kVpiScalarVal = vpiScalarVal;
constexpr int kVpiIntVal = vpiIntVal;
constexpr int kVpiRealVal = vpiRealVal;
constexpr int kVpiStringVal = vpiStringVal;
constexpr int kVpiTimeVal = vpiTimeVal;
constexpr int kVpiVectorVal = vpiVectorVal;
constexpr int kVpiStrengthVal = vpiStrengthVal;
constexpr int kVpiObjTypeVal = vpiObjTypeVal;

constexpr int kVpiShortIntVal = vpiShortIntVal;
constexpr int kVpiLongIntVal = vpiLongIntVal;
constexpr int kVpiShortRealVal = vpiShortRealVal;
constexpr int kVpiRawTwoStateVal = vpiRawTwoStateVal;
constexpr int kVpiRawFourStateVal = vpiRawFourStateVal;

constexpr int kVpiOneValue = vpiOneValue;
constexpr int kVpiPropagateOff = vpiPropagateOff;

constexpr int kVpiUserAllocFlag = vpiUserAllocFlag;

constexpr int kVpiSimTime = vpiSimTime;
constexpr int kVpiScaledRealTime = vpiScaledRealTime;

constexpr int kCbValueChange = cbValueChange;
constexpr int kCbReadWriteSynch = cbReadWriteSynch;
constexpr int kCbEndOfSimulation = cbEndOfSimulation;
constexpr int kCbStmt = cbStmt;
constexpr int kCbAtStartOfSimTime = cbAtStartOfSimTime;
constexpr int kCbReadOnlySynch = cbReadOnlySynch;

constexpr int kCbAfterDelay = cbAfterDelay;
constexpr int kCbNextSimTime = cbNextSimTime;
constexpr int kCbNBASynch = cbNBASynch;
constexpr int kCbAtEndOfSimTime = cbAtEndOfSimTime;

constexpr int kCbEndOfCompile = cbEndOfCompile;
constexpr int kCbStartOfSimulation = cbStartOfSimulation;
constexpr int kCbError = cbError;
constexpr int kCbPLIError = cbPLIError;
constexpr int kCbTchkViolation = cbTchkViolation;
constexpr int kCbSignal = cbSignal;
constexpr int kCbStartOfSave = cbStartOfSave;
constexpr int kCbEndOfSave = cbEndOfSave;
constexpr int kCbStartOfRestart = cbStartOfRestart;
constexpr int kCbEndOfRestart = cbEndOfRestart;
constexpr int kCbStartOfReset = cbStartOfReset;
constexpr int kCbEndOfReset = cbEndOfReset;
constexpr int kCbEnterInteractive = cbEnterInteractive;
constexpr int kCbExitInteractive = cbExitInteractive;
constexpr int kCbInteractiveScopeChange = cbInteractiveScopeChange;
constexpr int kCbUnresolvedSystf = cbUnresolvedSystf;

constexpr int kVpiType = vpiType;
constexpr int kVpiName = vpiName;
constexpr int kVpiFullName = vpiFullName;
constexpr int kVpiSize = vpiSize;
constexpr int kVpiDirection = vpiDirection;
constexpr int kVpiDefName = vpiDefName;

constexpr int kVpiAutomatic = vpiAutomatic;

constexpr int kVpiAllocScheme = vpiAllocScheme;

constexpr int kVpiAutomaticScheme = vpiAutomaticScheme;
constexpr int kVpiDynamicScheme = vpiDynamicScheme;
constexpr int kVpiOtherScheme = vpiOtherScheme;

constexpr int kVpiActualBySimTime = 0;
constexpr int kVpiActualStaticElab = 1;
constexpr int kVpiActualFrameVar = 2;
constexpr int kVpiActualLexicalDefn = 3;
constexpr int kVpiActualClassTypespec = 4;
constexpr int kVpiActualTaskFuncVar = 5;

constexpr int kVpiLibrary = vpiLibrary;
constexpr int kVpiConfig = vpiConfig;
constexpr int kVpiCell = vpiCell;

constexpr int kVpiInput = vpiInput;
constexpr int kVpiOutput = vpiOutput;
constexpr int kVpiInout = vpiInout;

constexpr int kVpiNoDelay = vpiNoDelay;
constexpr int kVpiInertialDelay = vpiInertialDelay;
constexpr int kVpiTransportDelay = vpiTransportDelay;
constexpr int kVpiPureTransportDelay = vpiPureTransportDelay;

constexpr int kVpiFinish = vpiFinish;
constexpr int kVpiStop = vpiStop;
constexpr int kVpiReset = vpiReset;
constexpr int kVpiSetInteractiveScope = vpiSetInteractiveScope;

constexpr int kVpi0 = vpi0;
constexpr int kVpi1 = vpi1;
constexpr int kVpiX = vpiX;
constexpr int kVpiZ = vpiZ;

constexpr int kVpiNotice = vpiNotice;
constexpr int kVpiWarning = vpiWarning;
constexpr int kVpiError = vpiError;
constexpr int kVpiSystem = vpiSystem;
constexpr int kVpiInternal = vpiInternal;

constexpr int kVpiRunSaveRestartId = 1;

constexpr int kVpiCompile = vpiCompile;
constexpr int kVpiPLI = vpiPLI;
constexpr int kVpiRun = vpiRun;

struct VpiDelayInfo {
  double delay = 0.0;
  double min_delay = 0.0, typ_delay = 0.0, max_delay = 0.0;
  double reject = 0.0;
  double min_reject = 0.0, typ_reject = 0.0, max_reject = 0.0;
  double error = 0.0;
  double min_error = 0.0, typ_error = 0.0, max_error = 0.0;
};

}  // namespace delta
