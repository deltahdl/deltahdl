// §35.4 and §35.5.4: binding a design's imported subroutines to the foreign
// functions their linkage names name. Every imported subroutine resolves to a
// global symbol, and the tool binds the declaration to it; Annex J has that
// symbol arrive in a shared library loaded before the run.
#ifndef DELTA_SIMULATOR_DPI_BINDING_H_
#define DELTA_SIMULATOR_DPI_BINDING_H_

#include <filesystem>
#include <functional>
#include <string>

#include "common/diagnostic.h"
#include "simulator/dpi_runtime.h"
#include "simulator/sim_context.h"

namespace delta {

// The address of the global symbol a name names, or nullptr where there is
// none.
using DpiSymbolLookup = std::function<void*(const std::string&)>;

// §35.4: binds each import of `dpi` to the function `lookup` finds under its
// linkage name, calling it with the prototype §H.8 gives the declaration (see
// dpi_c_call.h). The calls are generated as C source and built with the C
// compiler `compiler` in the directory `work_dir`, which is removed again once
// they are loaded. An import whose symbol is not found is left unbound, for
// §35.5.4's report at a call to it. So is one whose symbol is found but which
// cannot be called in C here, and one whose calls could not be built, each
// with the reason in DpiRtFunction::unbound_reason; a build that fails is
// reported as well, with what the compiler printed.
void BindDpiImports(DpiRuntime& dpi, const DpiSymbolLookup& lookup,
                    const std::filesystem::path& work_dir,
                    const std::string& compiler, DiagEngine& diag);

// The run's binding: every import the design registered in `ctx`, looked up
// among the global symbols of the process -- the libraries Annex J loaded
// among them -- and called through code the system's C compiler `cc` builds
// in a directory under the system's temporary directory. A design that
// declares no import has nothing to bind.
void BindDesignDpiImports(SimContext& ctx);

}  // namespace delta

#endif  // DELTA_SIMULATOR_DPI_BINDING_H_
