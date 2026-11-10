#pragma once

#include <cstddef>
#include <cstdint>
#include <iosfwd>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"
#include "lexer/token.h"
#include "simulator/assoc_index.h"

namespace delta {

struct AssocArrayObject;
struct ClassTypeInfo;
struct DataType;
enum class DataTypeKind : uint8_t;
struct EnumTypeInfo;
struct Expr;
struct ModuleItem;
struct Stmt;
struct StructFieldInfo;
struct StructMember;
struct StructTypeInfo;
struct TimeFormatSpec;
struct Net;
struct NetStrength;
struct QueueObject;
struct Variable;
class SimContext;
class Arena;

Logic4Vec EvalExpr(const Expr* expr, SimContext& ctx, Arena& arena,
                   uint32_t context_width = 0);

uint32_t LiteralWidth(std::string_view text, uint64_t val);

uint32_t DeclaredTypeWidth(const DataType& type, SimContext& ctx);

uint32_t NamedMemberWidth(const StructMember& m, SimContext& ctx);

uint32_t RunningDimsWidth(const DataType& type, SimContext& ctx);

bool DeclaredTypeIsString(const DataType& type, const SimContext& ctx);

bool DeclaredTypeIsReal(const DataType& type, const SimContext& ctx);

Logic4Vec ToDeclaredReal(const Logic4Vec& value, const DataType* type,
                         SimContext& ctx, Arena& arena);

bool DeclaredTypeIsSigned(const DataType& type, const SimContext& ctx);

DataTypeKind DeclaredTypeKind(const DataType& type, const SimContext& ctx);

void RecordDeclaredRange(const DataType& type, Variable* v, SimContext& ctx,
                         Arena& arena);

bool HasUnknownBits(const Logic4Vec& v);

bool NameDenotesVariable(std::string_view name, SimContext& ctx);

bool ClassScopeDeclares(std::string_view name, SimContext& ctx);
Logic4Vec MakeAllX(Arena& arena, uint32_t width);

Logic4Vec MakeAllHighZ(Arena& arena, uint32_t width);
int64_t SignExtend(uint64_t val, uint32_t width);

inline constexpr int64_t kBeyondEveryBound = int64_t{1} << 62;
int64_t SelectBoundValue(const Logic4Vec& val);

int64_t LongintValue(const Logic4Vec& val);

Logic4Vec NonexistentQueueElement(const QueueObject* q, Arena& arena);

Logic4Vec NonexistentElementOf(const Expr* select, bool is_4state,
                               uint32_t elem_width, SimContext& ctx,
                               Arena& arena);

void TakeElementSignedness(const QueueObject& q, Logic4Vec& val);

void TakeElementSignedness(const AssocArrayObject& aa, Logic4Vec& val);

double RealVecToDouble(const Logic4Vec& v);

double RealValueOf(const Logic4Vec& v);

Logic4Vec MakeRealVec(Arena& arena, double val, uint32_t width);

AssocIndex AssocIntKey(const Logic4Vec& val, bool is_wildcard,
                       uint32_t index_width, bool is_signed = true);

std::string AssocStringKey(const Logic4Vec& val);

std::pair<uint32_t, uint32_t> SelectRange(const Expr* expr, SimContext& ctx,
                                          Arena& arena);

bool CollectUnpackedSliceElements(const Expr* expr, SimContext& ctx,
                                  Arena& arena, std::vector<Logic4Vec>& out);

Logic4Vec EvalSelect(const Expr* expr, SimContext& ctx, Arena& arena);

Logic4Vec EvalUtilitySysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::string_view name);

Logic4Vec EvalIOSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                        std::string_view name);

Logic4Vec EvalMathSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                          std::string_view name);

Logic4Vec EvalFileIOSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            std::string_view name);

Logic4Vec EvalArrayQuerySysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                std::string_view name);

Logic4Vec EvalSampledArg(const Expr* arg, SimContext& ctx, Arena& arena);

Logic4Vec EvalVerifSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           std::string_view name);

bool TryEvalPlaSystemTask(const Expr* expr, SimContext& ctx, Arena& arena);

bool TryEvalStringMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out);

bool TryEvalStringMethodOnValue(const Logic4Vec& value, const Expr* call_expr,
                                SimContext& ctx, Arena& arena, Logic4Vec& out);

bool PropertyIsString(const ClassTypeInfo* type, std::string_view name,
                      SimContext& ctx, bool elements = false);

void RecordVariableEnumType(std::string_view var_name, const DataType& type,
                            SimContext& ctx);

const EnumTypeInfo* EnumTypeOfExpr(const Expr* e, SimContext& ctx,
                                   Arena& arena);

const EnumTypeInfo* EnumTypeOfDataType(const DataType& type, SimContext& ctx);

bool TryEvalEnumMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out);
bool TryEvalEnumMethodWithoutArgs(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out);

bool TryEvalArrayMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out);
bool TryExecArrayMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena);

Logic4Vec AssembleConcatParts(const std::vector<Logic4Vec>& parts,
                              uint32_t total_width, Arena& arena);

Logic4Vec EvalBinaryOp(TokenKind op, Logic4Vec lhs, Logic4Vec rhs, Arena& arena,
                       uint32_t context_width = 0);

TokenKind CompoundAssignBaseOp(TokenKind op);
bool IsCompoundAssignOp(TokenKind op);
Logic4Vec EvalCompoundAssign(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalReplicate(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalPrefixUnary(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalPostfixUnary(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalMemberAccess(const Expr* expr, SimContext& ctx, Arena& arena);
std::string HierarchicalReferenceName(const Expr* expr);
std::string RootedReferenceKey(const std::string& name);
std::string RootedReferenceKey(const Expr* expr);
Net* FindHierarchicalNet(const Expr* expr, SimContext& ctx);
std::string_view ArrayRootKey(const Expr* base, Arena& arena);
Logic4Vec EvalCast(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalInside(const Expr* expr, SimContext& ctx, Arena& arena);
bool CollectUnpackedSetMembers(const Expr* elem, SimContext& ctx,
                               std::vector<Logic4Vec>& out);
int EvalInsideElement(const Logic4Vec& lhs, const Expr* elem, SimContext& ctx,
                      Arena& arena);
Logic4Vec EvalStreamingConcat(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec PackBitStreamOperand(const Expr* arg, SimContext& ctx, Arena& arena);
Logic4Vec EvalAssignmentPattern(const Expr* expr, SimContext& ctx,
                                Arena& arena);
std::optional<Logic4Vec> EvalPackedArrayPattern(const Expr* pattern,
                                                std::span<const uint32_t> spans,
                                                uint32_t width, SimContext& ctx,
                                                Arena& arena);

Logic4Vec EvalStructPattern(const Expr* expr, const StructTypeInfo* info,
                            SimContext& ctx, Arena& arena);
Logic4Vec EvalStructMemberValue(const Expr* elem, const StructFieldInfo& field,
                                SimContext& ctx, Arena& arena);

uint32_t StreamSliceSize(const Expr* size_expr, SimContext& ctx, Arena& arena);

Logic4Vec EvalItemForLayout(const Expr* item, const StructTypeInfo* layout,
                            SimContext& ctx, Arena& arena);

Logic4Vec EvalDefaultForElement(const Expr* value, const StructTypeInfo* layout,
                                SimContext& ctx, Arena& arena);

void ApplyLayoutDefaults(Logic4Vec& value, const StructTypeInfo& layout,
                         uint32_t base, SimContext& ctx, Arena& arena);
void ApplyVariableLayoutDefaults(std::string_view name, Variable* var,
                                 SimContext& ctx, Arena& arena);
Logic4Vec EvalStructPatternValue(const Expr* expr, const StructTypeInfo* info,
                                 SimContext& ctx, Arena& arena);
Logic4Vec EvalMatches(const Expr* expr, SimContext& ctx, Arena& arena);

Logic4Vec EvalSystemCall(const Expr* expr, SimContext& ctx, Arena& arena);

bool SystemCallNamesARegisteredTask(const Expr* expr);

const TimeScale& ActiveInstanceTimeScale(const SimContext& ctx);

std::string BuildPrinttimescaleReport(const Expr* expr, SimContext& ctx);

std::string BuildStackTraceReport(const SimContext& ctx);
Logic4Vec EvalFunctionCall(const Expr* expr, SimContext& ctx, Arena& arena);

void RegisterBlockLet(const Stmt* stmt, SimContext& ctx);
bool BlockDeclaresLet(const Stmt* block);
void RegisterInstanceLet(SimContext& ctx, std::string_view prefix,
                         ModuleItem* let);
ModuleItem* FindVisibleLet(SimContext& ctx, std::string_view name);
Logic4Vec EvalLetExpansion(ModuleItem* decl, const Expr* call, SimContext& ctx,
                           Arena& arena, uint32_t context_width = 0);
uint64_t CurrentLetInstance();
uint32_t CallContextWidth();
uint32_t SetCallContextWidth(uint32_t width);

void EmitSeverityHeader(SimContext& ctx, std::string_view prefix,
                        std::string_view msg, std::ostream& os,
                        SourceLoc loc = SourceLoc::None());

const ModuleItem* SetupTaskCall(const Expr* expr, SimContext& ctx,
                                Arena& arena);
void TeardownTaskCall(const ModuleItem* func, const Expr* expr, SimContext& ctx,
                      Arena& arena);

Logic4Vec EvalClassNew(std::string_view class_type, const Expr* new_expr,
                       SimContext& ctx, Arena& arena, SourceLoc loc);

bool TryEvalTypedConstructorNew(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out);

struct ClassTypeInfo;
struct ClassObject;
bool TryClassScopeEnumLiteral(std::string_view name, const ClassTypeInfo* cls,
                              Arena& arena, Logic4Vec& out);

Logic4Vec ClassEnumLiteral(const ClassTypeInfo& cls, const std::string& name,
                           uint64_t value, Arena& arena);

void BindClassParams(const ClassTypeInfo* cls, const Expr* base_id,
                     SimContext& ctx, Arena& arena);

const ClassTypeInfo* PackageQualifiedClassOf(const Expr* expr, SimContext& ctx,
                                             std::string_view& member);

bool TryPackageClassStaticMember(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out);

void ApplyClassParamOverrides(std::string_view var_name, uint64_t handle,
                              SimContext& ctx, Arena& arena);

void BindSpecializationTypeParams(ClassObject* obj);

class DiagEngine;
struct ModuleItem;
void ValidateRefLifetime(const ModuleItem* func, DiagEngine& diag);

void ValidateConstRefWriteProtection(const ModuleItem* func, DiagEngine& diag);

Logic4Vec StringToLogic4Vec(Arena& arena, std::string_view str);

std::string Logic4VecToString(const Logic4Vec& vec);

struct MethodCallParts {
  std::string_view var_name;
  std::string_view method_name;
  SourceLoc loc = SourceLoc::None();
};
bool ExtractMethodCallParts(const Expr* expr, MethodCallParts& out);

struct DisplayFormatOpts {
  const std::vector<std::string>* p_fmts = nullptr;
  const TimeFormatSpec* time_format = nullptr;
  const std::vector<std::string>* v_fmts = nullptr;
  const std::vector<char>* arg_nonscalar_net = nullptr;
  SimContext* ctx = nullptr;
  const std::vector<char>* arg_unpacked_agg = nullptr;
  const std::vector<std::string>* arg_byte_strings = nullptr;
  SourceLoc loc;
};

std::string FormatDisplay(const std::string& fmt,
                          const std::vector<Logic4Vec>& vals,
                          const DisplayFormatOpts& opts = {});
std::string FormatArg(const Logic4Vec& val, char spec);
std::string FormatArgAutoSized(const Logic4Vec& val, char spec);
std::string FormatStrength(const NetStrength& ns);
std::string FormatTimeUnderTimeformat(const Logic4Vec& val,
                                      const TimeFormatSpec& spec,
                                      int value_order);
std::string FormatValueAsString(const Logic4Vec& val);
std::string ExtractFormatString(const Expr* first_arg);
size_t CountFormatConversions(std::string_view fmt);

Logic4Vec EvalUnbasedUnsized(const Expr* expr, Arena& arena);

Logic4Vec FillUnbasedUnsized(const Logic4Vec& v, uint32_t width, Arena& arena);
const Expr* StringLiteralSource(const Expr* expr);
uint8_t StringLiteralByteAt(const Logic4Vec& packed, uint32_t i);
Logic4Vec EvalIntLiteral(const Expr* expr, Arena& arena,
                         uint32_t context_width = 0);
std::string_view StringLiteralBody(std::string_view text);
Logic4Vec EvalStringLiteral(const Expr* expr, Arena& arena);

}  // namespace delta
