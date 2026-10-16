#pragma once

#include <functional>
#include <string_view>
#include <vector>

namespace delta {

class SimContext;
struct Expr;
struct RtlirContAssign;
struct VpiObject;

// §37.3.4: the delay expression vpiDelay reaches from an object whose source
// code wrote `delays`, in the order written, the first null entry ending the
// list. Each delay stands as a vpiConstant holding the value it evaluates to in
// the instance whose names are keyed under `scope_prefix` (dotted, empty for a
// top-level module's); one delay is that constant, several are a vpiOperation
// of vpiOpType vpiListOp over them, and none is null. `alloc` makes each
// object.
VpiObject* VpiSourceDelayExpression(const std::vector<const Expr*>& delays,
                                    std::string_view scope_prefix,
                                    SimContext& ctx,
                                    const std::function<VpiObject*()>& alloc);

// §37.47 with §37.3.4 and §10.3.3: the delays the continuous assignment `ca`
// was written with, set on its object `obj` twice over: in ticks, as
// vpi_get_delays reads them -- a rise, a fall that is the rise where none was
// written, and a turn-off that is the smaller of the two where none was -- and
// as the expression vpiDelay reaches, evaluated in the instance under
// `scope_prefix`. Nothing for an assignment written with no delay.
void VpiFillContAssignDelays(VpiObject* obj, const RtlirContAssign& ca,
                             std::string_view scope_prefix, SimContext& ctx,
                             const std::function<VpiObject*()>& alloc);

}  // namespace delta
