#ifndef DELTA_SIMULATOR_DPI_EXPORT_H_
#define DELTA_SIMULATOR_DPI_EXPORT_H_

#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "simulator/sim_context.h"

namespace delta {

std::string DpiInstanceScopeName(std::string_view prefix,
                                 const SimContext& ctx);

void RegisterModuleDpiExports(const RtlirModule* mod, std::string_view prefix,
                              SimContext& ctx);

}  // namespace delta

#endif
