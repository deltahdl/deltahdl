#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/packed_range.h"
#include "elaborator/const_eval.h"
#include "lexer/token.h"

namespace delta {

struct DataType;
struct RtlirParamDecl;
struct RtlirUnpackedDim;
struct ModuleItem;
struct Stmt;

struct ConstVal {
  int64_t value;
  uint32_t width;
  bool is_signed;
  std::vector<uint64_t> high_words = {};
};

ConstVal NormalizeConstVal(int64_t value, uint32_t width, bool is_signed);

struct FoldContext {
  uint32_t width = 0;
  bool read_unsigned = false;
};

std::optional<ConstVal> ConstEvalFull(const Expr* expr, const ScopeMap& scope,
                                      FoldContext ctx);
std::optional<ConstVal> ConstEvalBinaryFull(const Expr* expr,
                                            const ScopeMap& scope,
                                            FoldContext ctx);
std::optional<ConstVal> ConstEvalUnaryFull(const Expr* expr,
                                           const ScopeMap& scope,
                                           FoldContext ctx);
std::optional<ConstVal> ConstEvalFull(const Expr* expr, const ScopeMap& scope);
std::optional<ConstVal> ConstEvalLiteral(const Expr* expr);
std::optional<const Stmt*> ConstFuncCaseArm(const Stmt* s,
                                            const ScopeMap& locals);

struct LocalNames {
  std::unordered_set<std::string_view> declared;
  std::unordered_map<std::string_view, double> reals;
  std::unordered_map<std::string_view, std::optional<std::string>> strings;
};

class LocalNameFrame {
 public:
  LocalNameFrame();
  explicit LocalNameFrame(std::string_view genvar);
  ~LocalNameFrame();
  LocalNameFrame(const LocalNameFrame&) = delete;
  LocalNameFrame& operator=(const LocalNameFrame&) = delete;
  LocalNameFrame(LocalNameFrame&&) = delete;
  LocalNameFrame& operator=(LocalNameFrame&&) = delete;

 private:
  LocalNames locals_;
  LocalNames* prev_;
};
void DeclareLocalName(std::string_view name);
bool DeclaresLocalName(std::string_view name);
std::optional<double> ConstFuncRealLocal(std::string_view name);
void SetConstFuncRealLocal(std::string_view name, double value);
void ClearConstFuncRealLocal(std::string_view name);
const std::optional<std::string>* ConstFuncStringLocal(std::string_view name);
void SetConstFuncStringLocal(std::string_view name,
                             std::optional<std::string> chars);
std::optional<std::string> NamedStringChars(const Expr* expr,
                                            const ScopeMap& scope);
void ReportConstFuncSeverity(const Expr* call, const ScopeMap& locals,
                             DiagEngine& diag, Arena& arena);
bool IsConstFuncRealType(const DataType& type);
std::optional<bool> ConstFuncTruth(const Expr* cond, const ScopeMap& scope);
const ModuleItem* RegisteredConstFunc(const Expr* call);
std::optional<bool> LetCallIsConstant(const Expr* call, const ScopeMap& scope);
std::optional<ConstVal> ConstEvalLetCall(const Expr* call,
                                         const ScopeMap& scope,
                                         FoldContext ctx);
std::optional<double> ConstEvalUserCallReal(const Expr* call,
                                            const ScopeMap& scope);
std::optional<ConstVal> ConstEvalUnbasedUnsized(const Expr* expr,
                                                FoldContext ctx);
std::optional<ConstVal> ConstEvalStringLiteral(const Expr* expr,
                                               const ScopeMap& scope);

std::optional<std::string> ConstTypenameChars(const Expr* expr);

std::optional<ConstVal> ConstEvalTernaryFull(const Expr* expr,
                                             const ScopeMap& scope,
                                             FoldContext ctx);

std::optional<ConstVal> ConstEvalCastFull(const Expr* expr,
                                          const ScopeMap& scope);

ConstVal ReadInContext(const ConstVal& v, FoldContext ctx);

struct BinaryOperands {
  ConstVal lhs;
  ConstVal rhs;
};

std::optional<BinaryOperands> FoldBinaryOperands(const Expr* expr,
                                                 const ScopeMap& scope,
                                                 FoldContext ctx);

bool AnswersOneBit(TokenKind op);

FoldContext DeclaredFoldContext(const RtlirParamDecl& pd);

std::optional<int64_t> FoldParamValue(const RtlirParamDecl& pd,
                                      const Expr* expr, const ScopeMap& scope);
std::optional<int64_t> EvalConstSysCall(const Expr* expr,
                                        const ScopeMap& scope);

std::optional<ConstVal> ConstEvalConcatFull(const Expr* expr,
                                            const ScopeMap& scope);
std::optional<ConstVal> ConstEvalReplicateFull(const Expr* expr,
                                               const ScopeMap& scope);

std::optional<ConstVal> ConstEvalSelectFull(const Expr* expr,
                                            const ScopeMap& scope);

std::vector<uint64_t> LiteralHighWords(std::string_view text, uint32_t width);

std::optional<uint64_t> BasedLiteralLowWord(std::string_view text);

class TwoStateLiteralGuard {
 public:
  explicit TwoStateLiteralGuard(bool on);
  ~TwoStateLiteralGuard();
  TwoStateLiteralGuard(const TwoStateLiteralGuard&) = delete;
  TwoStateLiteralGuard& operator=(const TwoStateLiteralGuard&) = delete;

 private:
  bool prev_;
};

bool UnknownDigitsReadAsZero();

std::optional<int64_t> FindTwoStateReading(const ScopeMap& scope,
                                           std::string_view name);

bool ConstValBit(const ConstVal& v, int64_t offset);

bool SizedByLeftOperand(TokenKind op);

bool BinaryResultSigned(TokenKind op, const ConstVal& lhs, const ConstVal& rhs);

std::optional<ConstVal> EvalWideBinary(TokenKind op, const ConstVal& lhs,
                                       const ConstVal& rhs, uint32_t width);

std::optional<ConstVal> EvalWideMultiplicative(TokenKind op,
                                               const ConstVal& lhs,
                                               const ConstVal& rhs,
                                               uint32_t width);

std::vector<uint64_t> ExtendedWords(const ConstVal& v, uint32_t width,
                                    bool sign_extend);

ConstVal ConstValOfWords(const std::vector<uint64_t>& words, uint32_t width,
                         bool is_signed);

void AddWords(std::vector<uint64_t>& acc, const std::vector<uint64_t>& addend);

void NegateWords(std::vector<uint64_t>& words);

void ClearBitsFrom(std::vector<uint64_t>& words, uint32_t width);

std::vector<uint64_t> WordsOfHalves(const std::vector<uint32_t>& halves);

std::optional<ConstVal> EvalWideUnary(TokenKind op, const ConstVal& operand);

bool ConstValIsNonZero(const ConstVal& v);

ConstVal CastConstVal(const ConstVal& v, uint32_t width, bool is_signed);

const RtlirParamDecl* RegisteredParamNamed(std::string_view name);

ScopeMap RegisteredModuleScope();

const DataType* RegisteredTypedef(std::string_view name);
const std::unordered_map<std::string_view, DataType>&
RegisteredTypedefsOrNone();
uint32_t RegisteredTypeWidth(const DataType& type, const ScopeMap& scope);

std::optional<int64_t> RegisteredTypeRefCompare(const Expr* expr);

bool IsArrayQueryFunction(std::string_view name);
bool IsDynamicallySized(const Expr* arg);
std::optional<RtlirUnpackedDim> FoldUnpackedDimBounds(const Expr* dim,
                                                      const ScopeMap& scope);
std::optional<int64_t> EvalConstArrayQuery(const Expr* expr,
                                           const ScopeMap& scope);

uint32_t ConstLiteralWidth(const Expr* expr);

std::optional<int64_t> EvalConstBits(const Expr* expr, const ScopeMap& scope);

std::optional<ConstVal> RegisteredParamValue(std::string_view name,
                                             int64_t value);

void RecordResolvedHighWords(RtlirParamDecl& pd, const Expr* expr,
                             const ScopeMap& scope);

const std::vector<std::string_view>& RegisteredGenPrefixes();

const RtlirModule* RegisteredModule();

bool AllElementsConstant(const std::vector<Expr*>& elems,
                         const ScopeMap& scope);

std::optional<ConstVal> ConstEvalBuiltinMethodFull(const Expr* expr,
                                                   const ScopeMap& scope);

struct SpecializationArg {
  bool supplied = false;
  std::optional<ConstVal> value;
};

SpecializationArg ConstEvalSpecializedClassParam(const Expr* expr,
                                                 const ScopeMap& scope);

bool NamesSpecializedClassParam(const Expr* expr);

std::optional<double> ConstEvalSpecializedClassParamReal(const Expr* expr,
                                                         const ScopeMap& scope);

std::optional<std::string> ConstEvalSpecializedClassParamString(
    const Expr* expr, const ScopeMap& scope);

std::optional<bool> BuiltinMethodCallIsConstant(const Expr* expr,
                                                const ScopeMap& scope);

std::optional<std::string> ScopedNameKey(const Expr* expr);

bool NamesAggregateParam(const Expr* expr);

bool NamesScalarUnitParam(const Expr* expr);

std::optional<ConstVal> ConstEvalAggregatePart(const Expr* expr,
                                               const ScopeMap& scope);

std::optional<double> ConstEvalAggregatePartReal(const Expr* expr,
                                                 const ScopeMap& scope);

std::optional<std::string> ConstEvalAggregatePartString(const Expr* expr,
                                                        const ScopeMap& scope);

bool IsRealAggregatePart(const Expr* expr);

struct PackedSelectBase {
  PackedRange range;
  uint32_t element_width = 1;
  bool element_signed = false;
};

std::optional<PackedSelectBase> PackedSelectBaseOf(const Expr* expr,
                                                   const ScopeMap& scope);

}  // namespace delta
