#pragma once

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/dpi.h"

namespace delta {

using SvBit = uint8_t;
using SvScalar = uint8_t;

using SvLogic = uint8_t;

using SvBitVecVal = uint32_t;

struct SvLogicVecVal {
  uint32_t aval = 0;
  uint32_t bval = 0;
};

using SvChandle = void*;

struct SvOpenArrayHandle {
  void* data = nullptr;
  uint32_t size = 0;
  uint32_t elem_width = 0;
};

struct DpiScope {
  std::string name;
  std::string_view module_name;
  void* user_data = nullptr;
};

struct DpiArgValue {
  DataTypeKind type = DataTypeKind::kInt;
  union {
    int32_t int_val;
    int64_t longint_val;
    double real_val;
    SvChandle chandle_val;
    SvBit bit_val;
    SvLogic logic_val;
  } data = {};
  std::string string_val;

  static DpiArgValue FromInt(int32_t v);
  static DpiArgValue FromLongint(int64_t v);
  static DpiArgValue FromReal(double v);
  static DpiArgValue FromString(std::string v);
  static DpiArgValue FromChandle(SvChandle v);
  static DpiArgValue FromBit(SvBit v);
  static DpiArgValue FromLogic(SvLogic v);

  int32_t AsInt() const;
  int64_t AsLongint() const;
  double AsReal() const;
  const std::string& AsString() const;
  SvChandle AsChandle() const;
  SvBit AsBit() const;
  SvLogic AsLogic() const;
};

using DpiRtCallback =
    std::function<DpiArgValue(const std::vector<DpiArgValue>&)>;

struct DpiRtFunction {
  std::string_view c_name;
  std::string_view sv_name;
  DataTypeKind return_type = DataTypeKind::kVoid;
  std::vector<DpiArg> args;
  DpiRtCallback impl;
  bool is_pure = false;
  bool is_context = false;
};

struct DpiRtExport {
  std::string_view c_name;
  std::string_view sv_name;
  DpiRtCallback impl;
};

class DpiRuntime {
 public:

  void RegisterImport(DpiRtFunction func);
  const DpiRtFunction* FindImport(std::string_view sv_name) const;
  bool HasImport(std::string_view sv_name) const;
  uint32_t ImportCount() const;

  void RegisterExport(DpiRtExport exp);
  const DpiRtExport* FindExport(std::string_view sv_name) const;
  bool HasExport(std::string_view sv_name) const;
  uint32_t ExportCount() const;

  DpiArgValue CallImport(std::string_view sv_name,
                         const std::vector<DpiArgValue>& args) const;

  DpiArgValue CallExport(std::string_view sv_name,
                         const std::vector<DpiArgValue>& args) const;

  void PushScope(DpiScope scope);
  void PopScope();
  const DpiScope* CurrentScope() const;
  void SetScope(const DpiScope* scope);
  const DpiScope* GetScope() const;

  static uint32_t SvLow(const SvOpenArrayHandle& h);
  static uint32_t SvHigh(const SvOpenArrayHandle& h);
  static uint32_t SvSize(const SvOpenArrayHandle& h);

 private:
  std::vector<DpiRtFunction> imports_;
  std::unordered_map<std::string_view, size_t> import_index_;
  std::vector<DpiRtExport> exports_;
  std::unordered_map<std::string_view, size_t> export_index_;
  std::vector<DpiScope> scope_stack_;
  const DpiScope* current_scope_ = nullptr;
};

enum class AssertionSeverity : uint8_t {
  kInfo = 0,
  kWarning = 1,
  kError = 2,
  kFatal = 3,
};

enum class AssertionAction : uint8_t {
  kNone = 0,
  kPass = 1,
  kFail = 2,
  kDisable = 3,
  kEnable = 4,
  kReset = 5,
  kKill = 6,
};

struct AssertionCbData {
  int reason = 0;
  AssertionSeverity severity = AssertionSeverity::kError;
  AssertionAction action = AssertionAction::kNone;
  std::string_view assertion_name;
  void* user_data = nullptr;
};

using AssertionCbFunc = std::function<void(const AssertionCbData&)>;

constexpr int kCbAssertionStart = 601;
constexpr int kCbAssertionSuccess = 602;
constexpr int kCbAssertionFailure = 603;
constexpr int kCbAssertionDisabled = 604;
constexpr int kCbAssertionReset = 605;
constexpr int kCbAssertionKilled = 606;

class AssertionApi {
 public:
  void RegisterCallback(int reason, AssertionCbFunc cb, void* user_data);
  void FireCallback(const AssertionCbData& data);
  uint32_t CallbackCount() const;

  void SetSeverity(std::string_view name, AssertionSeverity sev);
  AssertionSeverity GetSeverity(std::string_view name) const;

  void SetAction(std::string_view name, AssertionAction action);
  AssertionAction GetAction(std::string_view name) const;

 private:
  struct CbEntry {
    int reason = 0;
    AssertionCbFunc cb;
    void* user_data = nullptr;
  };
  std::vector<CbEntry> callbacks_;
  std::unordered_map<std::string, AssertionSeverity> severity_map_;
  std::unordered_map<std::string, AssertionAction> action_map_;
};

enum class CoverageControl : uint8_t {
  kStop = 0,
  kStart = 1,
  kReset = 2,
  kCheck = 3,
};

class CoverageApi {
 public:
  void SetControl(CoverageControl ctrl);
  CoverageControl GetControl() const;

  void SetMaxBins(uint32_t max_bins);
  uint32_t GetMaxBins() const;

  void SetActive(bool active);
  bool IsActive() const;

  void StoreValue(std::string_view key, double value);
  double GetValue(std::string_view key) const;

 private:
  CoverageControl control_ = CoverageControl::kStart;
  uint32_t max_bins_ = 64;
  bool active_ = true;
  std::unordered_map<std::string, double> values_;
};

enum class DataReadFormat : uint8_t {
  kBinStr = 1,
  kOctStr = 2,
  kHexStr = 3,
  kScalar = 4,
  kInt = 5,
  kReal = 6,
  kString = 7,
  kVector = 8,
  kStrength = 9,
};

struct DataReadValue {
  DataReadFormat format = DataReadFormat::kInt;
  int32_t int_val = 0;
  double real_val = 0.0;
  std::string str_val;
  uint32_t scalar_val = 0;
  std::vector<SvLogicVecVal> vector_val;
};

using ValueChangeCb =
    std::function<void(std::string_view, const DataReadValue&)>;

class DataReadApi {
 public:

  DataReadValue GetValue(std::string_view name, DataReadFormat fmt) const;

  void PutValue(std::string_view name, const DataReadValue& val);

  void RegisterValueChangeCb(std::string_view name, ValueChangeCb cb);
  void NotifyValueChange(std::string_view name, const DataReadValue& val);
  uint32_t ValueChangeCbCount() const;

  void StoreVariable(std::string_view name, const DataReadValue& val);

 private:
  std::unordered_map<std::string, DataReadValue> variables_;
  std::unordered_map<std::string, std::vector<ValueChangeCb>> change_cbs_;
};

}
