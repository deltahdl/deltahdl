#pragma once

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"
#include "simulation/dpi.h"

namespace delta {

// =============================================================================
// svdpi.h type mapping (IEEE 1800-2023 S35.5)
// =============================================================================

// Two-state scalar types.
using svBit = uint8_t;
using svScalar = uint8_t;

// Four-state scalar types.
using svLogic = uint8_t;

// Packed array element types.
using svBitVecVal = uint32_t;

struct svLogicVecVal {
  uint32_t aval = 0;
  uint32_t bval = 0;
};

// Chandle: opaque pointer to C data.
using svChandle = void*;

// Open array handle (S35.5.6).
struct svOpenArrayHandle {
  void* data = nullptr;
  uint32_t size = 0;
  uint32_t elem_width = 0;
};

// =============================================================================
// DPI scope management (IEEE 1800-2023 S35.5.4)
// =============================================================================

struct DpiScope {
  std::string name;
  std::string_view module_name;
  void* user_data = nullptr;
};

// =============================================================================
// DpiArgValue: typed argument for DPI calls
// =============================================================================

struct DpiArgValue {
  DataTypeKind type = DataTypeKind::kInt;
  union {
    int32_t int_val;
    int64_t longint_val;
    double real_val;
    svChandle chandle_val;
    svBit bit_val;
    svLogic logic_val;
  } data = {};
  std::string string_val;

  static DpiArgValue FromInt(int32_t v);
  static DpiArgValue FromLongint(int64_t v);
  static DpiArgValue FromReal(double v);
  static DpiArgValue FromString(std::string v);
  static DpiArgValue FromChandle(svChandle v);
  static DpiArgValue FromBit(svBit v);
  static DpiArgValue FromLogic(svLogic v);

  int32_t AsInt() const;
  int64_t AsLongint() const;
  double AsReal() const;
  const std::string& AsString() const;
  svChandle AsChandle() const;
  svBit AsBit() const;
  svLogic AsLogic() const;
};

// =============================================================================
// DpiRtFunction: runtime DPI-C function with typed arguments
// =============================================================================

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

// =============================================================================
// DpiRtExport: runtime DPI-C export registration
// =============================================================================

struct DpiRtExport {
  std::string_view c_name;
  std::string_view sv_name;
  DpiRtCallback impl;  // The SV-side implementation.
};

// =============================================================================
// DpiRuntime: full DPI-C runtime manager (S35)
// =============================================================================

class DpiRuntime {
 public:
  // Import management.
  void RegisterImport(DpiRtFunction func);
  const DpiRtFunction* FindImport(std::string_view sv_name) const;
  bool HasImport(std::string_view sv_name) const;
  uint32_t ImportCount() const;

  // Export management.
  void RegisterExport(DpiRtExport exp);
  const DpiRtExport* FindExport(std::string_view sv_name) const;
  bool HasExport(std::string_view sv_name) const;
  uint32_t ExportCount() const;

  // Call an import function with typed arguments.
  DpiArgValue CallImport(std::string_view sv_name,
                         const std::vector<DpiArgValue>& args) const;

  // Invoke an export function from C side.
  DpiArgValue CallExport(std::string_view sv_name,
                         const std::vector<DpiArgValue>& args) const;

  // Scope management (S35.5.4).
  void PushScope(DpiScope scope);
  void PopScope();
  const DpiScope* CurrentScope() const;
  void SetScope(const DpiScope* scope);
  const DpiScope* GetScope() const;

  // Open array support (S35.5.6).
  static uint32_t SvLow(const svOpenArrayHandle& h);
  static uint32_t SvHigh(const svOpenArrayHandle& h);
  static uint32_t SvSize(const svOpenArrayHandle& h);

 private:
  std::vector<DpiRtFunction> imports_;
  std::unordered_map<std::string_view, size_t> import_index_;
  std::vector<DpiRtExport> exports_;
  std::unordered_map<std::string_view, size_t> export_index_;
  std::vector<DpiScope> scope_stack_;
  const DpiScope* current_scope_ = nullptr;
};

// =============================================================================
// Assertion API (IEEE 1800-2023 S39)
// =============================================================================

// Assertion severity levels (S39.5.1).
enum class AssertionSeverity : uint8_t {
  kInfo = 0,
  kWarning = 1,
  kError = 2,
  kFatal = 3,
};

// Assertion action types (S39.5.2).
enum class AssertionAction : uint8_t {
  kNone = 0,
  kPass = 1,
  kFail = 2,
  kDisable = 3,
  kEnable = 4,
  kReset = 5,
  kKill = 6,
};

// Assertion callback data (S39.5.3).
struct AssertionCbData {
  int reason = 0;
  AssertionSeverity severity = AssertionSeverity::kError;
  AssertionAction action = AssertionAction::kNone;
  std::string_view assertion_name;
  void* user_data = nullptr;
};

// Assertion callback type.
using AssertionCbFunc = std::function<void(const AssertionCbData&)>;

// Assertion callback reason constants (S39.5).
constexpr int kCbAssertionStart = 601;
constexpr int kCbAssertionSuccess = 602;
constexpr int kCbAssertionFailure = 603;
constexpr int kCbAssertionDisabled = 604;
constexpr int kCbAssertionReset = 605;
constexpr int kCbAssertionKilled = 606;

// Assertion API context.
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

// =============================================================================
// Coverage API (IEEE 1800-2023 S40)
// =============================================================================

// Coverage control constants (S40.3).
enum class CoverageControl : uint8_t {
  kStop = 0,
  kStart = 1,
  kReset = 2,
  kCheck = 3,
};

// Coverage API context.
class CoverageApi {
 public:
  void SetControl(CoverageControl ctrl);
  CoverageControl GetControl() const;

  void SetMaxBins(uint32_t max_bins);
  uint32_t GetMaxBins() const;

  void SetActive(bool active);
  bool IsActive() const;

  // Coverage data access.
  void StoreValue(std::string_view key, double value);
  double GetValue(std::string_view key) const;

 private:
  CoverageControl control_ = CoverageControl::kStart;
  uint32_t max_bins_ = 64;
  bool active_ = true;
  std::unordered_map<std::string, double> values_;
};

// =============================================================================
// Data Read API (IEEE 1800-2023 S41)
// =============================================================================

// Value format identifiers for the data read API (S41.3).
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

// Data read value container.
struct DataReadValue {
  DataReadFormat format = DataReadFormat::kInt;
  int32_t int_val = 0;
  double real_val = 0.0;
  std::string str_val;
  uint32_t scalar_val = 0;
  std::vector<svLogicVecVal> vector_val;
};

// Value change callback.
using ValueChangeCb =
    std::function<void(std::string_view, const DataReadValue&)>;

// Data read API context.
class DataReadApi {
 public:
  // Read a variable's value (S41.4).
  DataReadValue GetValue(std::string_view name, DataReadFormat fmt) const;

  // Write a variable's value (S41.5).
  void PutValue(std::string_view name, const DataReadValue& val);

  // Register a value-change callback (S41.6).
  void RegisterValueChangeCb(std::string_view name, ValueChangeCb cb);
  void NotifyValueChange(std::string_view name, const DataReadValue& val);
  uint32_t ValueChangeCbCount() const;

  // Internal variable storage for standalone testing.
  void StoreVariable(std::string_view name, const DataReadValue& val);

 private:
  std::unordered_map<std::string, DataReadValue> variables_;
  std::unordered_map<std::string, std::vector<ValueChangeCb>> change_cbs_;
};

}  // namespace delta
