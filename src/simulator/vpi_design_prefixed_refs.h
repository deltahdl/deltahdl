#pragma once

#include <functional>
#include <string>
#include <string_view>

#include "simulator/vpi_design_attach_build.h"

namespace delta {

class SimContext;
struct VpiObject;

// §37.48 details 2 and 3: `vif.cb` written in an expression, where `holder`
// is the virtual interface var `vif` and `written` the whole dotted name it
// heads: a clocking block whose vpiPrefix is the var, where the interface the
// var's declaration names declares a clocking block of that name; null for
// any other member.
VpiObject* VpiVirtualInterfaceClockingBlock(
    VpiObject* holder, std::string_view written,
    const std::function<VpiObject*()>& alloc, const VpiNameKeeper& keep);

// §37.29: where `type` is vpiActual and `ref` a virtual interface var holding
// a value in the run `ctx`, sets its actual to what it refers to now: the
// interface instance the handle it holds names, found by its name through
// `by_name`, and null while it holds none. Leaves any other object, or one with
// no run or no value, as it is.
void VpiRefreshVirtualInterfaceActual(
    int type, VpiObject& ref, SimContext* ctx,
    const std::function<VpiObject*(const std::string&)>& by_name);

// §37.48 detail 3: where `type` is vpiActual and `ref` a clocking block a
// virtual interface var prefixes, sets its actual to what it stands for now:
// the block of its name the interface instance the var holds in the run `ctx`
// declares, that instance found by its name through `by_name`, and null while
// the var holds none. Leaves any other object, or one with no run, as it is.
void VpiRefreshPrefixedClockingBlock(
    int type, VpiObject& ref, SimContext* ctx,
    const std::function<VpiObject*(const std::string&)>& by_name);

}  // namespace delta
