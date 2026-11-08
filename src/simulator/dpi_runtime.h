#pragma once

#include <cstddef>
#include <cstdint>
#include <deque>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"

namespace delta {

inline constexpr int32_t kDpiNoTimescale = INT32_MIN;

struct DpiScope {
  std::string name;
  std::string_view module_name;
  void* user_data = nullptr;
  int32_t time_unit = kDpiNoTimescale;
  int32_t time_precision = kDpiNoTimescale;
};

enum class DpiPackedArgPassing : uint8_t {
  kCanonical,
  kSv31aReference,
};

enum class DpiCompatibilityLevel : uint8_t { kIeee1800, kSv31a };

DpiCompatibilityLevel DpiCompatibilityLevelOf(std::string_view sv_dpi_version);
bool DpiOpaqueHandlesAreRequiredForAllPackedArguments(
    DpiCompatibilityLevel level);
DpiPackedArgPassing DpiPassingSemanticsOfSpecString(
    std::string_view dpi_spec_string);
bool DpiSv31aDefinitionsAreObligatoryInSvdpiH();
bool DpiCCodeMayFailToBind(bool implementation_supports_sv31a_functionality);

enum class DpiApplicationCompatibility : uint8_t { kBinary, kSource };

DpiApplicationCompatibility DpiCompatibilityOfApplication(bool uses_svdpi_src);
bool DpiApplicationIsRecompiledPerSimulator(bool uses_svdpi_src);
uint32_t DpiSvdpiSrcSymbolCount();
bool DpiPackedArrayMacroMayDefineAnArrayType();

bool DpiSvdpiSrcIsNeededForExportCall(
    bool allocates_representation_dynamically);

struct DpiRtFunction {
  std::string_view c_name;
  std::string_view sv_name;
  DataTypeKind return_type = DataTypeKind::kVoid;
  bool return_is_unsigned = false;
  std::vector<DpiArg> args;
  DpiRtCallback impl;
  DpiRtArgCallback arg_impl;
  bool is_pure = false;
  bool is_context = false;
  bool is_task = false;
  DpiPackedArgPassing packed_arg_passing = DpiPackedArgPassing::kCanonical;
  std::string unbound_reason;
};

struct DpiRtExport {
  std::string_view c_name;
  std::string_view sv_name;
  std::string scope_name;
  DpiRtCallback impl;
  DpiRtArgCallback arg_impl;
  bool is_context = true;
  bool is_task = false;
  DataTypeKind return_type = DataTypeKind::kVoid;
  std::vector<DpiArg> args;
};

std::string_view DpiGlobalName(const DpiRtFunction& func);
std::string_view DpiGlobalName(const DpiRtExport& exp);

enum class DpiExportCallStatus : uint8_t {
  kOk,
  kNoncontextChain,
  kScopeMismatch,
  kFunctionCallsTask,
  kDisabledStateExportCall,
};

enum class DpiDisableTarget : uint8_t {
  kNone,
  kExportItself,
  kAncestor,
};

bool DpiCurrentDisabledState();
void DpiSetCurrentDisabledState(bool disabled);
void DpiAckCurrentDisable();
bool DpiCurrentDisableAcknowledged();

const DpiScope* DpiRegisterScope(std::string_view name);
const DpiScope* DpiScopeFromName(std::string_view name);
const char* DpiNameFromScope(const DpiScope* scope);
bool DpiScopeIsValid(const DpiScope* scope);

void DpiSetScopeTimescale(const DpiScope* scope, int32_t time_unit,
                          int32_t time_precision);
bool DpiScopeTimescale(const DpiScope* scope, int32_t* time_unit,
                       int32_t* time_precision);

class DpiRuntime {
 public:
  void RegisterImport(DpiRtFunction func);
  std::vector<DpiRtFunction>& Imports() { return imports_; }
  std::vector<DpiRtExport>& Exports() { return exports_; }
  const DpiRtFunction* FindImport(std::string_view sv_name) const;
  const DpiRtFunction* FindImportIn(std::string_view unit_scope,
                                    std::string_view sv_name) const;
  bool HasImport(std::string_view sv_name) const;
  uint32_t ImportCount() const;

  void RegisterExport(DpiRtExport exp);
  const DpiRtExport* FindExport(std::string_view sv_name) const;

  const DpiRtExport* FindExportInScope(std::string_view sv_name,
                                       std::string_view scope_name) const;
  bool HasExport(std::string_view sv_name) const;
  uint32_t ExportCount() const;

  const DpiRtFunction* FindImportByGlobalName(
      std::string_view global_name) const;
  const DpiRtExport* FindExportByGlobalName(std::string_view global_name) const;

  bool HasGlobalName(std::string_view global_name) const;

  uint32_t GlobalNameCount() const;

  DpiArgValue CallImport(std::string_view sv_name,
                         const std::vector<DpiArgValue>& args) const;

  static DpiArgValue UndeterminedOutputValue(DataTypeKind type,
                                             uint32_t width = 0);

  DpiArgValue CallImportWithArgs(std::string_view sv_name,
                                 std::vector<DpiArgValue>& actuals) const;

  DpiArgValue CallImportDetectingChanges(
      std::string_view sv_name, std::vector<DpiArgValue>& actuals,
      std::vector<DpiArgValueChange>& changes) const;

  DpiArgValue CallExport(std::string_view sv_name,
                         const std::vector<DpiArgValue>& args) const;

  bool ImportCallIsRemovable(std::string_view sv_name) const;

  DpiArgValue CallImportReusingPureResult(std::string_view sv_name,
                                          const std::vector<DpiArgValue>& args);

  void PushScope(DpiScope scope);
  void PopScope();
  const DpiScope* CurrentScope() const;
  void SetScope(const DpiScope* scope);
  const DpiScope* GetScope() const;
  bool HoldsScope(const DpiScope* scope) const;

  void EnterContextImportCall(std::string_view sv_name, DpiScope decl_scope,
                              bool is_task = false);
  void EnterNoncontextImportCall(std::string_view sv_name,
                                 bool is_task = false);

  void EnterDeclaredImportCall(std::string_view sv_name, DpiScope decl_scope);

  void LeaveImportCall();
  uint32_t ImportCallDepth() const;
  bool ChainRootIsContext() const;

  bool InCallChain() const;
  uint32_t OpenCallChainCount() const;
  bool InContextCallChain() const;

  DpiExportCallStatus CallExportFromImport(
      std::string_view sv_name, const std::vector<DpiArgValue>& args,
      DpiArgValue* out_result, std::vector<DpiArgValue>* written = nullptr);

  std::string_view CurrentImportName() const {
    return call_chain_.empty() ? std::string_view()
                               : call_chain_.back().sv_name;
  }

  bool IsImportCallOptimizationBarrier(std::string_view sv_name) const;

  int ReturnFromExportUnderDisable(DpiDisableTarget target);

  void* PackedArgRef(std::string_view sv_name, void* actual_data) const;

  bool IsDisabledState() const;

  bool CheckImportedSubroutineDisableReturn(bool is_task,
                                            int task_return_value) const;

  bool VerifyImportReturnUnderDisable(int task_return_value);

  bool DisableProtocolFatalErrorIssued() const;
  const std::string& DisableProtocolFatalError() const;

  static int32_t SvLow(const SvOpenArrayHandle& h);
  static int32_t SvHigh(const SvOpenArrayHandle& h);
  static uint32_t SvSize(const SvOpenArrayHandle& h);

  static SvOpenArrayHandle MakeOpenArrayFromPackedActual(void* actual_data,
                                                         uint32_t actual_bits,
                                                         uint32_t elem_width);

  static uint32_t LinearizedPackedSize(
      const std::vector<SvActualDimension>& packed_dims);
  static SvOpenArrayHandle MakeOpenArrayFromPackedActual(
      void* actual_data, const std::vector<SvActualDimension>& packed_dims,
      uint32_t elem_width);

  static SvOpenArrayHandle MakeOpenArrayFromUnpackedActual(
      void* actual_data, SvActualDimension actual, uint32_t elem_width);

 private:
  bool VerifyImportTaskReturnUnderDisable(std::string_view sv_name,
                                          int task_return_value);

  bool VerifyImportFunctionReturnUnderDisable(std::string_view sv_name);

  void IssueDisableProtocolFatalError(const std::string& message);

  DpiExportCallStatus CheckExportCallPermitted(const DpiRtExport* exp,
                                               std::string_view sv_name);

  struct ImportFrame {
    std::string_view sv_name;
    bool is_context = false;
    bool is_task = false;
    const DpiScope* entry_scope = nullptr;
    bool entry_scope_from_stack = false;
  };

  std::vector<DpiRtFunction> imports_;
  std::unordered_map<std::string_view, size_t> import_index_;
  std::vector<DpiRtExport> exports_;
  std::unordered_map<std::string_view, size_t> export_index_;
  std::unordered_map<std::string, size_t> export_scope_index_;
  std::unordered_map<std::string_view, size_t> import_global_index_;
  std::unordered_map<std::string_view, size_t> export_global_index_;
  std::unordered_map<std::string, DpiArgValue> pure_results_;
  std::vector<const DpiScope*> scope_stack_;
  std::deque<DpiScope> unnamed_scopes_;
  const DpiScope* current_scope_ = nullptr;
  std::vector<ImportFrame> call_chain_;
  std::vector<size_t> chain_starts_;
  bool disable_protocol_fatal_ = false;
  std::string disable_protocol_fatal_message_;
};

void DpiSetForeignRuntime(DpiRuntime* runtime);
DpiRuntime* DpiForeignRuntime();

}  // namespace delta
