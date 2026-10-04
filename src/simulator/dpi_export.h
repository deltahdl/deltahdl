#ifndef DELTA_SIMULATOR_DPI_EXPORT_H_
#define DELTA_SIMULATOR_DPI_EXPORT_H_

#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "simulator/sim_context.h"

namespace delta {

// §35.5.3 with §H.9.3: the fully qualified name of the instance whose
// declarations the run keys under `prefix` -- "top" for the first top's own,
// keyed under no prefix, and "top.u1" for its instance keyed "u1.". A later
// top's keys already start with its name.
std::string DpiInstanceScopeName(std::string_view prefix,
                                 const SimContext& ctx);

// §35.7: registers each export `mod` declares, for the instance keyed under
// `prefix`, with the DPI runtime: under its SystemVerilog name and its linkage
// name, in the instance's scope, with the formals and result of the
// subroutine it exports. An exported function is run by calling it from the
// root of the design (CallDpiExportedFunction); an exported task is
// registered with nothing to run, a call from C that may enable one being
// one that has to suspend the import's C code (§35.8).
void RegisterModuleDpiExports(const RtlirModule* mod, std::string_view prefix,
                              SimContext& ctx);

}  // namespace delta

#endif  // DELTA_SIMULATOR_DPI_EXPORT_H_
