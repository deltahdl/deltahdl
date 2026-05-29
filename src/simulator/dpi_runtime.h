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
  // §35.5.3: the SystemVerilog scope where this export was declared. When
  // empty, the export is treated as callable from any chain scope (a
  // conservative default for code that doesn't yet record scopes).
  std::string scope_name;
  DpiRtCallback impl;
  // §35.7: every exported SystemVerilog function is a context function. The
  // flag is documentary at the type level and is normalized to true by
  // DpiRuntime::RegisterExport so callers that leave it unset still get the
  // spec-mandated behavior.
  bool is_context = true;
};

// §35.5.3: outcome of attempting to call a SystemVerilog export from inside
// a DPI import call chain. kOk means the call was permitted; kNoncontextChain
// reports the §35.5.3 error of a noncontext import trying to invoke an
// export. kScopeMismatch reports the §35.5.3 error of a context import call
// trying to invoke an export whose scope differs from the chain's current
// scope without first calling svSetScope.
enum class DpiExportCallStatus : uint8_t {
  kOk,
  kNoncontextChain,
  kScopeMismatch,
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

  // §35.5.3 call-chain instrumentation. A DPI import call chain begins when
  // SystemVerilog calls an import; the chain's context property comes from
  // the import's declaration. EnterContextImportCall/EnterNoncontextImportCall
  // push one frame each; the chain's "is_context" is the property of the
  // root (the bottom-most frame), and per the LRM context is not transitively
  // promoted to subsequent inner import calls.
  void EnterContextImportCall(std::string_view sv_name, DpiScope decl_scope);
  void EnterNoncontextImportCall(std::string_view sv_name);
  void LeaveImportCall();
  uint32_t ImportCallDepth() const;
  bool ChainRootIsContext() const;

  // §35.5.3: only context import calls (i.e., chains whose root is a context
  // import) can safely invoke a SystemVerilog export subroutine. Returns the
  // outcome and, on kOk, runs the export's registered implementation.
  DpiExportCallStatus CallExportFromImport(std::string_view sv_name,
                                           const std::vector<DpiArgValue>& args,
                                           DpiArgValue* out_result);

  // §35.5.3: reports whether a call to the named import would act as a
  // barrier for SystemVerilog compiler optimizations — true exactly when the
  // import is declared context. Optimizers query this to decide whether the
  // call may be folded or eliminated.
  bool IsImportCallOptimizationBarrier(std::string_view sv_name) const;

  static uint32_t SvLow(const SvOpenArrayHandle& h);
  static uint32_t SvHigh(const SvOpenArrayHandle& h);
  static uint32_t SvSize(const SvOpenArrayHandle& h);

 private:
  struct ImportFrame {
    std::string_view sv_name;
    bool is_context = false;
  };

  std::vector<DpiRtFunction> imports_;
  std::unordered_map<std::string_view, size_t> import_index_;
  std::vector<DpiRtExport> exports_;
  std::unordered_map<std::string_view, size_t> export_index_;
  std::vector<DpiScope> scope_stack_;
  const DpiScope* current_scope_ = nullptr;
  std::vector<ImportFrame> call_chain_;
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

}  // namespace delta
