#pragma once

#include <string>

namespace delta {

class SimContext;
struct Process;

std::string ScopeHierName(const SimContext& ctx);

std::string ProcessHierName(const Process& proc, const SimContext& ctx);

}  // namespace delta
