#ifndef DELTA_SIMULATOR_LOWERER_REGISTER_H_
#define DELTA_SIMULATOR_LOWERER_REGISTER_H_

namespace delta {

class Arena;
struct RtlirModule;
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
void RegisterModuleNets(const RtlirModule* mod, SimContext& ctx);
void RegisterModulePorts(const RtlirModule* mod, SimContext& ctx, Arena& arena);
void RegisterModuleSubroutines(const RtlirModule* mod, SimContext& ctx);
void RegisterModuleSequenceDecls(const RtlirModule* mod, SimContext& ctx);
void RegisterProcessClassType(SimContext& ctx, Arena& arena);

}  // namespace delta

#endif  // DELTA_SIMULATOR_LOWERER_REGISTER_H_
