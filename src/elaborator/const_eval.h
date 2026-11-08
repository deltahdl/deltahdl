#pragma once

#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/types.h"

namespace delta {

class Arena;
class DiagEngine;
struct Expr;
struct ModuleItem;
struct ClassDecl;
struct RtlirModule;
struct RtlirParamDecl;
struct DataType;

using ScopeMap = std::unordered_map<std::string_view, int64_t>;

class ConstFuncRegistryGuard {
 public:
  explicit ConstFuncRegistryGuard(
      const std::unordered_map<std::string_view, const ModuleItem*>* funcs);
  ~ConstFuncRegistryGuard();
  ConstFuncRegistryGuard(const ConstFuncRegistryGuard&) = delete;
  ConstFuncRegistryGuard& operator=(const ConstFuncRegistryGuard&) = delete;

 private:
  const std::unordered_map<std::string_view, const ModuleItem*>* prev_;
};

class ConstFuncSeverityGuard {
 public:
  ConstFuncSeverityGuard(DiagEngine& diag, Arena& arena);
  ~ConstFuncSeverityGuard();
  ConstFuncSeverityGuard(const ConstFuncSeverityGuard&) = delete;
  ConstFuncSeverityGuard& operator=(const ConstFuncSeverityGuard&) = delete;
  ConstFuncSeverityGuard(ConstFuncSeverityGuard&&) = delete;
  ConstFuncSeverityGuard& operator=(ConstFuncSeverityGuard&&) = delete;

 private:
  DiagEngine* prev_diag_;
  Arena* prev_arena_;
};

const std::unordered_map<std::string_view, const ModuleItem*>*
RegisteredConstFuncs();

class ParamClassRegistryGuard {
 public:
  explicit ParamClassRegistryGuard(
      const std::unordered_map<std::string_view, const ClassDecl*>* classes);
  ~ParamClassRegistryGuard();
  ParamClassRegistryGuard(const ParamClassRegistryGuard&) = delete;
  ParamClassRegistryGuard& operator=(const ParamClassRegistryGuard&) = delete;

 private:
  const std::unordered_map<std::string_view, const ClassDecl*>* prev_;
};

class ParamRangeRegistryGuard {
 public:
  explicit ParamRangeRegistryGuard(const RtlirModule* mod);
  ~ParamRangeRegistryGuard();
  ParamRangeRegistryGuard(const ParamRangeRegistryGuard&) = delete;
  ParamRangeRegistryGuard& operator=(const ParamRangeRegistryGuard&) = delete;

 private:
  const RtlirModule* prev_;
  std::vector<std::string_view> prev_scopes_;
};

using TypeRefComparer =
    std::function<std::optional<int64_t>(const Expr*, const RtlirModule*)>;
class TypedefRegistryGuard {
 public:
  TypedefRegistryGuard(
      const std::unordered_map<std::string_view, DataType>* typedefs,
      const std::unordered_set<std::string_view>* aggregate_names,
      const TypeRefComparer* compare = nullptr);
  ~TypedefRegistryGuard();
  TypedefRegistryGuard(const TypedefRegistryGuard&) = delete;
  TypedefRegistryGuard& operator=(const TypedefRegistryGuard&) = delete;

 private:
  const std::unordered_map<std::string_view, DataType>* prev_;
  const std::unordered_set<std::string_view>* prev_aggregate_names_;
  const TypeRefComparer* prev_compare_;
};

bool IsTypeRefComparison(const Expr* expr);

class RegisteredGenScopeGuard {
 public:
  explicit RegisteredGenScopeGuard(const std::vector<std::string_view>& scopes);
  ~RegisteredGenScopeGuard();
  RegisteredGenScopeGuard(const RegisteredGenScopeGuard&) = delete;
  RegisteredGenScopeGuard& operator=(const RegisteredGenScopeGuard&) = delete;

 private:
  std::vector<std::string_view> prev_;
};

class DelayModeGuard {
 public:
  explicit DelayModeGuard(DelayMode mode);
  ~DelayModeGuard();
  DelayModeGuard(const DelayModeGuard&) = delete;
  DelayModeGuard& operator=(const DelayModeGuard&) = delete;

 private:
  DelayMode prev_;
};

DelayMode ActiveDelayMode();

const Expr* SelectMinTypMaxMember(const Expr* expr);

std::optional<int64_t> ConstEvalInt(const Expr* expr);

std::optional<int64_t> ConstEvalInt(const Expr* expr, const ScopeMap& scope);

std::optional<int64_t> FoldDeclaredParamValue(const Expr* expr,
                                              const DataType& type,
                                              const ScopeMap& scope);

std::optional<int64_t> TwoStateReading(const Expr* expr, const DataType& type,
                                       const ScopeMap& scope, int64_t value);

void SetTwoStateReading(ScopeMap& scope, std::string_view name,
                        std::optional<int64_t> reading);

void BindDeclaredConstant(ScopeMap& scope, std::string_view name,
                          int64_t value);

std::optional<int64_t> RecordedTwoStateReading(const ScopeMap& scope,
                                               std::string_view name);

std::optional<int64_t> FoldParamValueAtWidth(const Expr* expr,
                                             const ScopeMap& scope,
                                             uint32_t width, bool is_signed);

uint32_t DeclaredParamTypeWidth(const DataType& type, const ScopeMap& scope);

struct ParamStorageShape {
  uint32_t width;
  bool is_signed;
};
ParamStorageShape ParamStorageShapeOf(const RtlirParamDecl& param);

std::optional<double> ConstEvalReal(const Expr* expr);
std::optional<double> ConstEvalReal(const Expr* expr, const ScopeMap& scope);

std::optional<std::string> ConstEvalString(const Expr* expr);

bool IsConstantExpr(const Expr* expr, const ScopeMap& scope);

bool IsConstantSysFunc(std::string_view name);

bool IsConstantWhateverItsArguments(const Expr* call);

const Expr* BuiltinMethodMember(const Expr* expr);

std::string LongestStaticPrefix(const Expr* expr, const ScopeMap& scope = {});

std::string LongestStaticStorageName(const Expr* expr);

}  // namespace delta
