#ifndef DELTA_SIMULATOR_DPI_BINDING_H_
#define DELTA_SIMULATOR_DPI_BINDING_H_

#include <filesystem>
#include <functional>
#include <string>

#include "common/diagnostic.h"
#include "simulator/dpi_runtime.h"
#include "simulator/sim_context.h"

namespace delta {

using DpiSymbolLookup = std::function<void*(const std::string&)>;

void BindDpiImports(DpiRuntime& dpi, const DpiSymbolLookup& lookup,
                    const std::filesystem::path& work_dir,
                    const std::string& compiler, DiagEngine& diag);

void BindDesignDpiImports(SimContext& ctx);

}  // namespace delta

#endif
