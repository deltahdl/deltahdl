#include "simulator/dpi_binding.h"

#include <unistd.h>

#include <cstddef>
#include <filesystem>
#include <memory>
#include <string>
#include <string_view>
#include <system_error>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_call.h"
#include "simulator/dpi_runtime.h"
#include "simulator/shared_library.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

// Gives `import` both forms of implementation, each calling `symbol` through
// `trampoline`: the direction-aware one CallImportWithArgs enters, and the
// input-only one a pure function's call is made through (§35.5.2), which
// hands the C function a copy of the arguments to write into.
void BindImport(DpiRtFunction& import, void* symbol, void* trampoline) {
  auto function = std::make_shared<const DpiCFunction>(
      DpiCFunction{import.args, import.return_type, import.is_task,
                   reinterpret_cast<void (*)()>(symbol),
                   reinterpret_cast<DpiCTrampoline>(trampoline)});
  import.arg_impl = [function](std::vector<DpiArgValue>& args) {
    return CallDpiCFunction(*function, args);
  };
  import.impl = [function](const std::vector<DpiArgValue>& args) {
    std::vector<DpiArgValue> copy = args;
    return CallDpiCFunction(*function, copy);
  };
}

// The design's exports the generated forwarders call into, in the order the
// forwarder source gave them their indices, and where the run's reports go.
struct DpiExportBinding {
  DpiRuntime* dpi = nullptr;
  std::vector<const DpiRtExport*> exports;
  DiagEngine* diag = nullptr;
};

DpiExportBinding& ExportBinding() {
  static DpiExportBinding binding;
  return binding;
}

// §35.5.3, §35.8: reports a call of `exp` the runtime refused, by the rule it
// broke. A call refused under §35.9 item d) was reported where it was refused.
void ReportRefusedExportCall(DpiExportCallStatus status, const DpiRtExport& exp,
                             const DpiRuntime& dpi, DiagEngine& diag) {
  const std::string kExport(exp.sv_name);
  const std::string kImport(dpi.CurrentImportName());
  switch (status) {
    case DpiExportCallStatus::kFunctionCallsTask:
      diag.Error(SourceLoc::None(),
                 "exported task '" + kExport +
                     "' enabled from imported function '" + kImport + "'",
                 Subclause("35.8"));
      break;
    case DpiExportCallStatus::kNoncontextChain:
      diag.Error(SourceLoc::None(),
                 "exported subroutine '" + kExport +
                     "' called from imported subroutine '" + kImport +
                     "', which is not declared context",
                 Subclause("35.5.3"));
      break;
    case DpiExportCallStatus::kScopeMismatch:
      diag.Error(SourceLoc::None(),
                 "exported subroutine '" + kExport +
                     "' called in a scope that declares no export of it",
                 Subclause("35.5.3"));
      break;
    default:
      break;
  }
}

// §35.7 with §H.8.2: the entry point every forwarder calls. The arguments are
// read out of the C objects the forwarder hands over, the export is called in
// the chain's current scope, and its outputs and result are laid back out in
// C's objects.
void DpiExportEntry(int index, void** args, void* result) {
  DpiExportBinding& binding = ExportBinding();
  if (binding.dpi == nullptr || index < 0 ||
      static_cast<std::size_t>(index) >= binding.exports.size()) {
    return;
  }
  const DpiRtExport& exp = *binding.exports[static_cast<std::size_t>(index)];
  const DataTypeKind kResult =
      exp.is_task ? DataTypeKind::kInt : exp.return_type;
  std::vector<DpiArgValue> values;
  for (std::size_t i = 0; i < exp.args.size(); ++i) {
    values.push_back(exp.args[i].direction == Direction::kOutput
                         ? DpiArgValue{}
                         : DpiValueOfCObject(exp.args[i], args[i]));
  }
  DpiArgValue returned;
  std::vector<DpiArgValue> written;
  const DpiExportCallStatus kStatus = binding.dpi->CallExportFromImport(
      exp.sv_name, values, &returned, &written);
  if (kStatus != DpiExportCallStatus::kOk) {
    ReportRefusedExportCall(kStatus, exp, *binding.dpi, *binding.diag);
    DpiStoreResultInCObject(kResult, DpiArgValue::FromInt(0), result);
    return;
  }
  if (exp.is_task) {
    // #4926: an exported task may consume time, which the import's C call
    // cannot be suspended for, so its body is not entered.
    binding.diag->Error(SourceLoc::None(),
                        "exported task '" + std::string(exp.sv_name) +
                            "' called from C is not run: deltahdl does not "
                            "yet suspend an imported task's C code",
                        Subclause("35.8"));
  }
  for (std::size_t i = 0; i < exp.args.size() && i < written.size(); ++i) {
    if (exp.args[i].direction != Direction::kInput) {
      DpiStoreInCObject(exp.args[i], written[i], args[i]);
    }
  }
  DpiStoreResultInCObject(kResult, returned, result);
}

// The exports of `dpi` foreign code can call, one per linkage name: the
// instances of one module's export share the name, and the chain's scope picks
// the instance a call reaches (§35.5.3).
std::vector<const DpiRtExport*> CallableExports(DpiRuntime& dpi) {
  std::vector<const DpiRtExport*> exports;
  std::unordered_set<std::string_view> names;
  for (const DpiRtExport& exp : dpi.Exports()) {
    if (!DpiExportNotCallableFromC(exp).empty()) continue;
    if (!names.insert(DpiGlobalName(exp)).second) continue;
    exports.push_back(&exp);
  }
  return exports;
}

}  // namespace

void BindDpiImports(DpiRuntime& dpi, const DpiSymbolLookup& lookup,
                    const std::filesystem::path& work_dir,
                    const std::string& compiler, DiagEngine& diag) {
  std::vector<DpiRtFunction*> callable;
  std::vector<const DpiRtFunction*> declarations;
  std::vector<void*> symbols;
  for (DpiRtFunction& import : dpi.Imports()) {
    void* symbol = lookup(std::string(DpiGlobalName(import)));
    if (symbol == nullptr) continue;
    import.unbound_reason = DpiImportNotCallableInC(import);
    if (!import.unbound_reason.empty()) continue;
    callable.push_back(&import);
    declarations.push_back(&import);
    symbols.push_back(symbol);
  }
  std::vector<const DpiRtExport*> exports = CallableExports(dpi);
  if (callable.empty() && exports.empty()) return;
  const SharedLibraryLoad kCalls = BuildAndLoadCSharedLibrary(
      DpiCTrampolineSource(declarations) + DpiCForwarderSource(exports),
      work_dir, compiler);
  if (kCalls.handle == nullptr) {
    diag.Error(SourceLoc::None(),
               "the calls into C of the design's imported subroutines could "
               "not be built: " +
                   kCalls.error,
               Subclause::None());
    for (DpiRtFunction* import : callable) {
      import->unbound_reason = "its call into C could not be built";
    }
    return;
  }
  for (std::size_t i = 0; i < callable.size(); ++i) {
    BindImport(*callable[i], symbols[i],
               SharedLibrarySymbol(kCalls.handle, DpiCTrampolineName(i)));
  }
  if (exports.empty()) return;
  // §35.7: the forwarders, global symbols now, call into the run through the
  // entry point installed here.
  ExportBinding() = DpiExportBinding{&dpi, std::move(exports), &diag};
  auto* install = reinterpret_cast<void (*)(DpiCExportEntry)>(
      SharedLibrarySymbol(kCalls.handle, DpiCExportEntrySetterName()));
  if (install != nullptr) install(&DpiExportEntry);
}

void BindDesignDpiImports(SimContext& ctx) {
  DpiRuntime* dpi = ctx.GetDpiRuntime();
  if (dpi == nullptr) return;
  std::error_code ec;
  const std::filesystem::path kWorkDir =
      std::filesystem::temp_directory_path(ec) /
      ("deltahdl-dpi-" + std::to_string(getpid()));
  BindDpiImports(*dpi, GlobalSymbol, kWorkDir, "cc", ctx.GetDiag());
}

}  // namespace delta
