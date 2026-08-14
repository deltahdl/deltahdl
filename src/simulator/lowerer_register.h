#ifndef DELTA_SIMULATOR_LOWERER_REGISTER_H_
#define DELTA_SIMULATOR_LOWERER_REGISTER_H_

#include <string_view>

namespace delta {

class Arena;
struct DataType;
struct RtlirModule;
struct RtlirPort;
class SimContext;
struct Variable;

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

// §11.5.1: record how a select on this storage resolves an index -- the
// outermost packed dimension of the declaration `dt` exactly as written, since
// "the actual bit that is accessed by an address is, in part, determined by the
// declaration". §7.4.1: when there is more than one packed dimension, also
// record the bit width of one outermost element, so a single-index select
// slices an element rather than a bit. A declaration with no packed range (an
// `int`, a scalar, a string) and a null `dt` both leave the storage addressed
// as [width-1:0], as does a range whose folded bounds do not span the storage's
// width. Shared because the rule is a property of the declaration and not of
// what is declared: a net and a variable written with the same packed dimension
// address the same bit by the same index.
void RecordPackedRange(const DataType* dt, Variable* v, SimContext& ctx,
                       Arena& arena);

// Create the storage one port is read and written through, under the name it
// is keyed by. Every property a port's storage carries is set here, so a
// property given to a port is given to it wherever in the hierarchy the port
// sits: RegisterModulePorts passes the port's own name and
// CreateChildModulePorts in src/simulator/lowerer_child.cpp passes the name
// under its instance prefix, and the name is the only thing that differs.
void CreatePortVariable(std::string_view name, const RtlirPort& port,
                        SimContext& ctx, Arena& arena);

void RegisterModuleNets(const RtlirModule* mod, SimContext& ctx, Arena& arena);
void RegisterModulePorts(const RtlirModule* mod, SimContext& ctx, Arena& arena);
void RegisterModuleSubroutines(const RtlirModule* mod, SimContext& ctx);
void RegisterModuleSequenceDecls(const RtlirModule* mod, SimContext& ctx);
void RegisterProcessClassType(SimContext& ctx, Arena& arena);

}  // namespace delta

#endif  // DELTA_SIMULATOR_LOWERER_REGISTER_H_
