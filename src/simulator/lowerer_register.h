#ifndef DELTA_SIMULATOR_LOWERER_REGISTER_H_
#define DELTA_SIMULATOR_LOWERER_REGISTER_H_

#include <string_view>

namespace delta {

class Arena;
struct DataType;
struct RtlirDesign;
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

// §7.2.1: register the layout of every packed struct or union a typedef of the
// design names, keyed by that name, so a member select of a value held under
// the name can be resolved without a typedef table. The layouts a variable's
// declaration registers are keyed by the variable's own name and answer only
// for it; a value held in a class property (§8.3) is named by no variable and
// has this to ask instead.
void RegisterDesignTypeLayouts(const RtlirDesign* design, SimContext& ctx,
                               Arena& arena);

void RegisterModuleNets(const RtlirModule* mod, SimContext& ctx, Arena& arena);
void RegisterModulePorts(const RtlirModule* mod, SimContext& ctx, Arena& arena);
void RegisterModuleSubroutines(const RtlirModule* mod, SimContext& ctx);

// §35.5.4: put this module's imported subroutine declarations in the run's DPI
// registry, which is what a call to one reaches its declaration through. The
// registry is acquired on the first module that declares an import, so a design
// that declares none never makes one.
void RegisterModuleDpiImports(const RtlirModule* mod, SimContext& ctx);
// §35.5.4: the same for the declarations written in the scopes that are no
// module instance -- each package's body and the compilation unit -- which a
// call reaches through an import, the package scope resolution operator or
// the bare name.
void RegisterDesignScopeDpiImports(const RtlirDesign* design, SimContext& ctx);
// §26.3: each package's subroutines under their "pk::name" keys, the keys a
// call through the package scope resolution operator resolves by.
void RegisterPackageScopedSubroutines(const RtlirDesign* design,
                                      SimContext& ctx, Arena& arena);
// §6.19 with §26.3: each package's enumeration constants under their
// "pk.name" keys, the keys a read through the package scope resolution
// operator resolves by, each at the value its declaration folds to.
// §26.2 with §6.8: every package parameter with an initializer and every
// package variable, with or without one, is given storage under its
// "pk.name" key -- the variable at its declared type's width, state and
// signedness, a string or real registered as such, an integral variable
// without an initializer at §6.8's default -- so a write through the scope
// or an import lands and a read through either sees it.
void InitPackageDataVariables(const RtlirDesign* design, SimContext& ctx,
                              Arena& arena);

void RegisterPackageEnumConstants(const RtlirDesign* design, SimContext& ctx,
                                  Arena& arena);
// §6.18 with §8.25.1: each typedef name whose chain ends in a class, bound
// to that class after every class of the design is lowered.
void RegisterClassTypeAliases(const RtlirDesign* design, SimContext& ctx);
// §16.8 and §16.12: the module's named sequence and property declarations,
// which an instance of one is expanded from at the run.
void RegisterModuleSequenceDecls(const RtlirModule* mod, SimContext& ctx);
void RegisterProcessClassType(SimContext& ctx, Arena& arena);

}  // namespace delta

#endif  // DELTA_SIMULATOR_LOWERER_REGISTER_H_
