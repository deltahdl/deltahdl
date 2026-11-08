#pragma once

#include <array>
#include <functional>
#include <string_view>
#include <vector>

#include "simulator/vpi_constants.h"

namespace delta {

class SimContext;
struct Expr;
struct RtlirContAssign;
struct VpiObject;

VpiObject* VpiSourceDelayExpression(const std::vector<const Expr*>& delays,
                                    std::string_view scope_prefix,
                                    SimContext& ctx,
                                    const std::function<VpiObject*()>& alloc);

VpiDelayInfo VpiWrittenDelay(const Expr* delay, SimContext& ctx);

std::vector<VpiDelayInfo> VpiWrittenDelays(
    const std::array<const Expr*, 3>& delays, bool turn_off,
    std::string_view scope_prefix, SimContext& ctx);

void VpiFillContAssignDelays(VpiObject* obj, const RtlirContAssign& ca,
                             std::string_view scope_prefix, SimContext& ctx,
                             const std::function<VpiObject*()>& alloc);

}  // namespace delta
