#ifndef DELTA_SIMULATOR_LOWERER_REGISTER_H_
#define DELTA_SIMULATOR_LOWERER_REGISTER_H_

namespace delta {

class Arena;
struct RtlirModule;
struct RtlirPort;
class SimContext;

// Publishing one module's declarations into the simulation context, before any
// of its processes run: the nets and port storage a name can resolve to, the
// subroutines and sequences a call or reference can name, and the built-in
// process class type. Each is a straight walk of one list on the module, which
// is why they sit together and apart from the lowering of behaviour.
//
// RegisterModulePorts gives a port storage only when nothing has already
// created it, and starts that storage at the default initial value of the
// port's data type (§23.3.3.2, Table 6-7) so an unconnected input reads as its
// type's default rather than as whatever fresh storage happens to hold.
//
// PortDefaultsToZero is that decision on its own: true when the port's type
// defaults to a zero bit pattern, false when the x fresh storage already holds
// is the answer. It is shared because a child instance creates its own prefixed
// copy of every port, and the rule cannot depend on where in the hierarchy the
// port sits.
bool PortDefaultsToZero(const RtlirPort& port);

void RegisterModuleNets(const RtlirModule* mod, SimContext& ctx);
void RegisterModulePorts(const RtlirModule* mod, SimContext& ctx, Arena& arena);
void RegisterModuleSubroutines(const RtlirModule* mod, SimContext& ctx);
void RegisterModuleSequenceDecls(const RtlirModule* mod, SimContext& ctx);
void RegisterProcessClassType(SimContext& ctx, Arena& arena);

}  // namespace delta

#endif  // DELTA_SIMULATOR_LOWERER_REGISTER_H_
