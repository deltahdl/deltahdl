#include "simulator/dpi_binding.h"

#include <unistd.h>

#include <cstddef>
#include <filesystem>
#include <memory>
#include <string>
#include <system_error>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
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
  if (callable.empty()) return;
  const SharedLibraryLoad kCalls = BuildAndLoadCSharedLibrary(
      DpiCTrampolineSource(declarations), work_dir, compiler);
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
