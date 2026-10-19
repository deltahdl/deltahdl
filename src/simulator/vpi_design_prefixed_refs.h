#pragma once

#include <functional>
#include <string>
#include <string_view>

#include "simulator/vpi_design_attach_build.h"

namespace delta {

class SimContext;
struct VpiObject;

// §37.48 details 2 and 3: `vif.cb` written in an expression, where `holder`
// is the virtual interface var `vif` and `written` the whole name: a clocking
// block whose vpiPrefix is the var, where the interface the var's declaration
// names declares a clocking block of that name; null for any other member.
VpiObject* VpiVirtualInterfaceClockingBlock(
    VpiObject* holder, std::string_view written,
    const std::function<VpiObject*()>& alloc, const VpiNameKeeper& keep);

// §37.48 detail 3: what the clocking block `block`, prefixed by a virtual
// interface var, stands for now: the block of its name the interface instance
// the var holds in the run `ctx` declares, that instance found by its name
// through `by_name`; null while the var holds none.
VpiObject* VpiPrefixedClockingBlockActual(
    const VpiObject& block, SimContext& ctx,
    const std::function<VpiObject*(const std::string&)>& by_name);

}  // namespace delta
