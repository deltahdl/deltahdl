#pragma once

#include <cstddef>
#include <cstdint>
#include <iosfwd>
#include <string>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

namespace delta {

struct DataType;
struct Expr;
struct FunctionArg;
struct ModuleItem;
struct Stmt;
class SimContext;
class Arena;
struct Process;
struct StructTypeInfo;
struct Variable;

bool DeclaredTypeIs4State(const DataType& type, const SimContext& ctx);

struct StaticFrame {
  std::string_view name;
  bool is_static_sub = false;
};

Variable* CreateFuncLocalVar(std::string_view name, const DataType& type,
                             const Expr* init, SimContext& ctx, Arena& arena);

void ExecFuncVarDecl(const Stmt* stmt, StaticFrame frame, SimContext& ctx,
                     Arena& arena);

bool BindNamedLayout(std::string_view var_name, const DataType& type,
                     SimContext& ctx);

const StructTypeInfo* NamedLayout(const DataType& type, SimContext& ctx);

void ExecFuncBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);
bool TryFuncClassPropertyWrite(const Expr* lhs, const Logic4Vec& val,
                               SimContext& ctx, Arena& arena);

bool IsPrngSysCall(std::string_view name);
Logic4Vec EvalPrngCall(const Expr* expr, SimContext& ctx, Arena& arena,
                       std::string_view name);
bool IsDisplayOrWriteTask(std::string_view name);
void ExecDisplayWrite(const Expr* expr, SimContext& ctx, Arena& arena);
std::string RenderDisplayArgList(const Expr* expr, size_t first,
                                 char default_radix, SimContext& ctx,
                                 Arena& arena);
std::string FormatDisplayArgs(const Expr* expr, size_t fmt_index,
                              const std::string& fmt, SimContext& ctx,
                              Arena& arena);
std::string BuildFormatP(const Expr* arg, const Logic4Vec& val,
                         SimContext& ctx);
void ExecSeverityTask(const Expr* expr, SimContext& ctx, Arena& arena,
                      const char* prefix, std::ostream& os);
Logic4Vec EvalDeferredPrint(const Expr* expr, SimContext& ctx, Arena& arena);
bool IsStrobeTask(std::string_view name);
bool IsMonitorTask(std::string_view name);
Logic4Vec EvalMonitor(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalMonitorFlag(SimContext& ctx, Arena& arena, std::string_view name);
bool IsVcdSysCall(std::string_view name);
Logic4Vec EvalVcdSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                         std::string_view name);

struct ClassObject;
void BindFunctionArgs(const ModuleItem* func, const Expr* expr, SimContext& ctx,
                      Arena& arena);
int ResolveArgIndex(const ModuleItem* func, const Expr* expr, size_t param_idx);
bool TryEvalPatternActual(const FunctionArg& param, const Expr* actual,
                          SimContext& ctx, Arena& arena, Logic4Vec& out);
bool TryBindTaggedActual(const FunctionArg& param, const Expr* actual,
                         SimContext& ctx);
bool TryBindInlineAggregateFormal(const FunctionArg& param, SimContext& ctx);
bool TryBindNamedAggregateFormal(const FunctionArg& param, SimContext& ctx);
std::string_view FormalLayoutKey(const FunctionArg& param, SimContext& ctx);
uint32_t EvalFormalArgWidth(const DataType& dt, SimContext& ctx, Arena& arena);

struct ActualBindingCtx {
  const Expr* call;
  size_t positional_count;
  SimContext& ctx;
  Arena& arena;
};

Logic4Vec EvalDpiCall(const Expr* expr, SimContext& ctx, Arena& arena);

struct DpiImportCall {
  DpiRuntime* dpi = nullptr;
  const DpiRtFunction* import = nullptr;
  std::string_view callee;
  const Expr* expr = nullptr;
  std::vector<DpiArgValue> args;
  std::vector<DpiArgValueChange> changes;
  DpiArgValue result;
};

bool BeginDpiImportCall(const Expr* expr, SimContext& ctx, Arena& arena,
                        DpiImportCall& call);

void CallDpiImport(DpiImportCall& call);

Logic4Vec FinishDpiImportCall(DpiImportCall& call, SimContext& ctx,
                              Arena& arena);

Expr* DpiExportCall(std::string_view key, const DpiRtExport& exp,
                    const std::vector<DpiArgValue>& args, SimContext& ctx);

void ReadDpiExportOutputs(const Expr* call, const DpiRtExport& exp,
                          std::vector<DpiArgValue>& args, SimContext& ctx);

DpiArgValue CallDpiExportedFunction(std::string_view key,
                                    const DpiRtExport& exp,
                                    std::vector<DpiArgValue>& args,
                                    SimContext& ctx);

struct ClassTypeInfo;
struct MethodCallParts;

const DataType* ActualForParam(const std::vector<DataType>& actuals, size_t i,
                               std::string_view pname);

struct InstanceMethodInfo {
  ClassObject* obj = nullptr;
  ModuleItem* method = nullptr;
  const ClassTypeInfo* owner = nullptr;
};
bool ResolveInstanceMethod(const MethodCallParts& parts, SimContext& ctx,
                           InstanceMethodInfo& info);
bool ResolveMethodByDeclaredClass(ClassObject* obj,
                                  std::string_view declared_class,
                                  std::string_view method_name, SimContext& ctx,
                                  InstanceMethodInfo& info);

bool ResolveStaticThroughNull(std::string_view method_name,
                              std::string_view class_type, SimContext& ctx,
                              InstanceMethodInfo& info);

bool ResolveThroughNullHandle(const MethodCallParts& parts,
                              std::string_view class_type, SimContext& ctx,
                              InstanceMethodInfo& info);

void ReportNullHandleCall(std::string_view method_name, SourceLoc loc,
                          SimContext& ctx);
Logic4Vec RunInstanceMethod(const InstanceMethodInfo& info, const Expr* expr,
                            SimContext& ctx, Arena& arena);

std::string_view ScopedClassKey(const Expr* scope, Arena& arena);

bool ExtractHandleMethodCallParts(const Expr* expr, Arena& arena,
                                  MethodCallParts& out);

bool TryEvalMethodOnEvaluatedBase(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out);

bool ExtractHandleAccessParts(const Expr* access, Arena& arena,
                              MethodCallParts& out);

bool IsSuperNewRunByConstruction(const Expr* call, SimContext& ctx);

Logic4Vec ExecInstanceMethodCall(ModuleItem* method, ClassObject* obj,
                                 const Expr* expr, SimContext& ctx,
                                 Arena& arena);

struct ClassMethodTarget {
  ModuleItem* method = nullptr;
  const ClassTypeInfo* param_cls = nullptr;
};
void ExecClassMethod(ClassMethodTarget target, const Expr* expr,
                     SimContext& ctx, Arena& arena, Logic4Vec& out);

Variable* CreateMethodReturnVariable(ClassMethodTarget target, SimContext& ctx);

void RunStaticMethodInClassScope(ClassMethodTarget target, const Expr* expr,
                                 SimContext& ctx, Arena& arena, Logic4Vec& out);
bool TryEvalEnclosingStaticCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out);

bool TryEvalEnclosingInstanceCall(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out);

bool TryEvalRandomizeMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out);

bool TryEvalScopeRandomizeCall(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out);

bool TryEvalObjectSrandom(const Expr* expr, SimContext& ctx, Arena& arena,
                          Logic4Vec& out);

bool TryEvalObjectGetRandState(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out);
bool TryEvalObjectSetRandState(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out);

bool TryEvalObjectConstraintMode(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out);

bool TryEvalObjectRandMode(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out);

bool IsModeMethodCall(const Expr* expr);
void WritebackOutputArgs(const ModuleItem* func, const Expr* expr,
                         SimContext& ctx, Arena& arena);
Logic4Vec EvalDefaultInDeclScope(const Expr* default_value, SimContext& ctx,
                                 Arena& arena);
void ExecFunctionBody(const ModuleItem* func, const Expr* call,
                      Variable* ret_var, SimContext& ctx, Arena& arena);
void ShapeStringReturnVariable(const ModuleItem* func, Variable* ret_var,
                               SimContext& ctx, Arena& arena);
void ShapeClassReturnVariable(const ModuleItem* func, Variable* ret_var,
                              SimContext& ctx, Arena& arena);
bool TryFuncReturnClassNew(Expr* returned, std::string_view func_name,
                           SimContext& ctx, Arena& arena);
void WritebackQueueRefs(SimContext& ctx);
void WritebackAssocRefs(SimContext& ctx);

bool TryEvalProcessStaticCall(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out);
bool TryEvalProcessMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out);
bool TryEvalProcessMethodWithoutArgs(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out);

bool NamesProcessHandle(const Expr* recv, SimContext& ctx, Arena& arena);

struct ProcessMethodCall {
  Process* proc = nullptr;
  std::string_view method;
};
bool ResolveProcessMethodCall(const Expr* call, SimContext& ctx, Arena& arena,
                              ProcessMethodCall& out);

bool TryEvalEventTriggeredCall(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out);

}  // namespace delta
