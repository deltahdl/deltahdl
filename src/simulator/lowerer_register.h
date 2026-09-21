#ifndef DELTA_SIMULATOR_LOWERER_REGISTER_H_
#define DELTA_SIMULATOR_LOWERER_REGISTER_H_

#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"

namespace delta {

class Arena;
struct AssocArrayObject;
struct ClassTypeInfo;
struct DataType;
struct Expr;
struct QueueObject;
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

// §7.2.1: record the layout of the packed structure or union `dtype` for the
// storage held under `name`, `width` bits wide, so a member select of that
// name resolves to the run of bits the type lays the member out at. Nothing is
// recorded for a null type or one with no members. Shared for the same reason
// RecordPackedRange is: the layout is a property of the declared type and not
// of what is declared, so a net port of a packed structure (§23.2.2.3 with
// §6.7.1) lays its members out as a variable of the same type does. Defined in
// src/simulator/lowerer_var_layout.cpp with the layout builder it calls.
void RegisterAggregateLayout(std::string_view name, const DataType* dtype,
                             uint32_t width, SimContext& ctx, Arena& arena);

// §7.4.2 with §7.4.4: the elements of the fixed-size unpacked array `var`
// declares, each a variable of its own under `name` with its index in
// brackets, `name[i]` or `name[i][j]`, with the ArrayInfo under `name` that
// $size, foreach and every element select read the shape from, and each
// element at the value the declaration's initializer or §6.8's Table 6-7
// gives it. Nothing is made for a declaration with no unpacked extent. The
// unpacked bounds are read from `var` as the elaborator folded them, so a
// declaration outside any module -- a package's (CreatePackageDataVariables)
// -- folds them into a RtlirVariable of its own first. Defined in
// src/simulator/lowerer_var.cpp beside Lowerer::LowerVarAggregate, which
// makes a module's arrays through it.
void CreateArrayElements(std::string_view name, const RtlirVariable& var,
                         SimContext& ctx, Arena& arena);
// §7.4.2 with §10.9.1: the declaration's initializer distributed over the
// element variables already standing under `name`, made at their defaults
// by CreateArrayElements, each written in place -- the one Variable object
// every alias of the element shares (§26.6's export, AliasArray in
// lowerer_import.cpp). An element no item of the pattern reaches keeps what
// it holds. Defined in src/simulator/lowerer_var.cpp beside
// CreateArrayElements; InitPackageArray (lowerer_package_data.cpp) fills a
// package's or the unit's array through it once every export is bound.
void InitArrayElements(std::string_view name, const RtlirVariable& var,
                       SimContext& ctx, Arena& arena);
// §7.10 with §7.5.1: fills the queue or dynamic array `q` from a
// declaration's initializer `init`: a new[] constructor sizes it and copies
// the optional source, an assignment pattern or an unpacked array
// concatenation supplies its elements in order; a null initializer, or one of
// another shape, leaves it empty. Evaluated in the scope in force, which is
// the declaring scope's frame for a package's. Defined in
// src/simulator/lowerer_var.cpp, where Lowerer::LowerDynArrayInit fills a
// module's through it.
void InitQueueFromDeclInit(QueueObject* q, const Expr* init, SimContext& ctx,
                           Arena& arena);
// §7.9.11: gives the associative array `aa` the default and the keyed
// entries the assignment pattern `init` writes, `'{default: 7}` or
// `'{"k": 1, 2: 5}`; a null initializer, or one that is not a pattern,
// writes nothing. Defined in src/simulator/lowerer_var.cpp, where
// Lowerer::InitAssocDefault fills a module's through it.
void InitAssocFromDeclInit(const Expr* init, AssocArrayObject* aa,
                           SimContext& ctx, Arena& arena);

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
// §6.19.5 with §6.18: the enumeration behind each scoped typedef name the
// design records (RtlirDesign::type_enums), "C::name" or "P::name",
// registered in the enum table under that key with its member values folded
// against the unit's constants, so that a class property or a package
// variable declared with the name has an enumeration for the methods of
// §6.19.5 to walk. Defined in src/simulator/lowerer_var_layout.cpp.
void RegisterDesignEnumTypes(const RtlirDesign* design, SimContext& ctx,
                             Arena& arena);
// §26.3 with §8.4: each package variable declared with a class's name,
// recorded under its "pk.name" key as a handle of that class -- the package's
// own class, one an import of the package brings in, or the one a `q::C`
// wrote -- so that a `new` written to it through the package scope resolution
// operator constructs the class. Reached through RegisterDesignTypeLayouts,
// which registers the design's other declared-type facts ahead of every
// module. Defined in src/simulator/lowerer_package_class_vars.cpp.
void RegisterPackageClassVariables(const RtlirDesign* design, SimContext& ctx,
                                   Arena& arena);
// §3.12.1 with §8.3: each compilation-unit variable declared with a
// class's name, recorded under its bare name -- the name a module's `h =
// new` asks the class of, and the record CreateUnitDataVariables carries to
// the "$unit.name" key it gives the storage -- as a handle of that class:
// the unit's own class, one an import of the unit brings in, the one a
// `p::C` wrote, or the built-in process or weak_reference class, with the
// specialization the declaration wrote (§8.25). Ahead of the unit's
// storage, which is sized by the record, and after the packages', whose
// classes an import may name. Defined in src/simulator/lowerer_register.cpp.
void RegisterUnitClassVariables(const RtlirDesign* design, SimContext& ctx,
                                Arena& arena);

// §6.20.2: a parameter declared with a range or a type has the range of its
// declaration, unchanged by any override, and RtlirParamDecl::resolved_value
// holds its value in 64 bits with no x or z among them. `var` is the storage
// Lowerer::LowerParams gave `param` at the declared width, filled from that
// value; where the width is more than 64 bits, or the expression holds a
// literal with an x or a z in it (§5.7.1), this evaluates the value's own
// expression again at that width and stores the whole of it, unknown bits
// included. The expression is the declaration's initializer, read in the
// instance being built, or the instance override's (§23.10.2), read in the
// instantiating instance. One naming what has no storage at this point -- a
// subroutine, an enumeration constant, an imported name, a genvar -- leaves
// the storage as it was, the folded value being exact for every other value
// that fits 64 bits.
void ReevaluateParamValue(const RtlirParamDecl& param, Variable* var,
                          SimContext& ctx, Arena& arena);

// §6.20.2 (printed pages 126-127): the width and signedness a value
// parameter's storage takes. A parameter declared with a range has the range
// of its declaration, and one declared with a type and no range is of that
// type, whatever value either took, so both are stored at decl_width with
// the declaration's sign. One declared with neither, or with a bare `signed`,
// takes the type and range of its final value -- a logic vector as wide as
// that value's self-determined width, 13 bits for `parameter p1 = 13'h7e`,
// 3 for `newconst3 = 3'h4` and at least 32 for the unsized `newconst4 = 4`,
// the clause's own examples -- which the elaborator records with the value
// as RtlirParamDecl::value_width and value_is_signed (RecordResolvedHighWords
// in src/elaborator/const_eval_bits.cpp). Where it recorded none, the value
// not having folded, 32 bits with the declaration's sign, the implied range
// of an unsized value. Defined in src/simulator/lowerer_register.cpp.
struct ParamStorageShape {
  uint32_t width;
  bool is_signed;
};
ParamStorageShape ParamStorageShapeOf(const RtlirParamDecl& param);

void RegisterModuleNets(const RtlirModule* mod, SimContext& ctx, Arena& arena);
void RegisterModulePorts(const RtlirModule* mod, SimContext& ctx, Arena& arena);
void RegisterModuleSubroutines(const RtlirModule* mod, SimContext& ctx);
// §13.3 with §23.6: the same subroutines under the instance's prefixed key,
// "u1.tk", which a hierarchical enable from another instance resolves by.
void RegisterInstanceSubroutines(const RtlirModule* mod,
                                 const std::string& inst_prefix,
                                 SimContext& ctx, Arena& arena);
// §27.4 with §13.4 and §23.6: the subroutines the module's named generate
// block instances declare, under `key_prefix` and the instance's path,
// "blk[1].triple" for the top and "u1.blk[1].triple" under the instance
// prefix "u1.", which a call by hierarchical name resolves by, with the
// scope each body runs in -- the module instance `inst_prefix` and the
// block's own -- recorded under the same key.
void RegisterGenBlockSubroutines(const RtlirModule* mod,
                                 const std::string& key_prefix,
                                 const std::string& inst_prefix,
                                 SimContext& ctx, Arena& arena);
// §21.2.1.5 and §27.3: `path` as the levels of a hierarchical name, a loop
// generate block's instance with its index in brackets, `g[0].h`; empty for
// an empty path.
std::string GenBlockName(const HierPath& path);

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
// §26.2 with §6.8: every package parameter with an initializer and every
// package variable, with or without one, is given storage under its
// "pk.name" key -- the variable at its declared type's width, state and
// signedness, a class handle (§8.3) at a handle's 64 bits, a string or real
// registered as such, a named event (§15.5) marked as one, an integral
// variable without an initializer at §6.8's default, a queue or an
// associative array (§7.10, §7.8) with the object its methods and element
// selects operate on, a fixed-size array (§7.4.2) with its elements at their
// defaults, a semaphore (§15.3) with the bucket its methods operate on,
// holding the keys its declaration's new() names -- so a write through the
// scope or an import lands and a read through either sees it. The other
// initializers are left for InitPackageDataVariables. Defined in
// src/simulator/lowerer_package_data.cpp, as are CreateUnitDataVariables,
// InitPackageDataVariables and InitUnitDataVariables.
void CreatePackageDataVariables(const RtlirDesign* design, SimContext& ctx,
                                Arena& arena);
// §3.12.1 with §6.21: the same for every data item the compilation-unit
// scope declares, under its "$unit.name" key, which no module's own
// declaration is keyed by. After the packages', which §26.2 keeps from
// naming the unit's.
void CreateUnitDataVariables(const RtlirDesign* design, SimContext& ctx,
                             Arena& arena);
// §3.12.1 with §23.9: the unit's data items the module `mod` does not
// declare, each bound under `inst_prefix` to its "$unit.name" storage with
// the kinds the storage carries, the key a bare reference of the module's
// processes resolves to when the module's own scope and its imports hold
// no such name; a key either holds is left. Called by Lowerer::LowerImports
// for the top and for each instance, after the module's imports and before
// its declarations. Defined in src/simulator/lowerer_package_data.cpp.
void AliasUnitDataItems(const RtlirDesign* design, const RtlirModule* mod,
                        std::string_view inst_prefix, SimContext& ctx,
                        Arena& arena);
// §26.3 with §26.6: the per-name records and objects the storage under
// `qname` carries -- its class record, real registration, queue,
// associative array, fixed-size or dynamic array with its elements,
// semaphore, mailbox and structure or union layout -- given to the alias
// `key`, so that a method call, an element select, a member select or a
// `new` through the alias reaches the one object. Defined in
// src/simulator/lowerer_alias_kinds.cpp; the import's, the export's and the
// unit's aliases take it.
void AliasVariableKinds(std::string_view key, std::string_view qname,
                        SimContext& ctx, Arena& arena);
// Whether the module declares `name` itself, as a variable, a port or a
// net, the declarations LowerModule and LowerChildModules give storage
// under the instance prefix. Defined in src/simulator/lowerer_import.cpp.
bool ModuleDeclaresName(const RtlirModule* mod, std::string_view name);
// §26.2: each package's declaration assignments, evaluated in the package's
// scope into the storage CreatePackageDataVariables gave them, once every
// package's storage exists and its exports are bound (AliasPackageExports),
// a fixed-size array's distributed over its elements then (§7.4.2).
void InitPackageDataVariables(const RtlirDesign* design, SimContext& ctx,
                              Arena& arena);
// §3.12.1 with §26.2: the compilation unit's declaration assignments, into
// the storage CreateUnitDataVariables gave them, after the packages' and
// before any procedure starts.
void InitUnitDataVariables(const RtlirDesign* design, SimContext& ctx,
                           Arena& arena);
// §8.7 with §8.25 and §26.2: the object each package variable's or unit
// variable's `new` declaration assignment constructs, `C h = new;` or `G
// #(5) b = new;`, of the specialization the declaration wrote, once every
// class of the design is lowered and ahead of every module
// (Lowerer::ConstructDesignData in lowerer_data_init.cpp), since the other
// initializers run ahead of every class and §6.21 has a module's variable
// initialized at its declaration. Defined in
// src/simulator/lowerer_package_data.cpp.
void ConstructDataClassInitializers(const RtlirDesign* design, SimContext& ctx,
                                    Arena& arena);
// §26.6: every name a package exports, bound under the exporting package's
// key to the declaring package's registration -- a subroutine's "pk::name",
// a variable's, parameter's or enumeration constant's "pk.name" -- once
// those registrations exist and ahead of every import that reads one. The
// definition stands in lowerer_import.cpp beside the export walk.
void AliasPackageExports(const RtlirDesign* design, SimContext& ctx,
                         Arena& arena);
// §6.19 with §26.3: each package's enumeration constants under their
// "pk.name" keys, the keys a read through the package scope resolution
// operator resolves by, each at the value its declaration folds to.
void RegisterPackageEnumConstants(const RtlirDesign* design, SimContext& ctx,
                                  Arena& arena);
// §6.18 with §15.4.9 and §15.3.1: the name at the end of each typedef name's
// chain and each typedef item's own type, recorded for the run ahead of
// every class (Lowerer::LowerDesignData), so a class's static
// initialization knows a property declared through a typedef of `mailbox`
// or `semaphore` for one.
void RegisterTypeTargets(const RtlirDesign* design, SimContext& ctx);

// §6.18 with §8.25.1: each typedef name whose chain ends in a class, bound
// to that class after every class of the design is lowered; and, §8.3, each
// class's own typedef naming a class, bound under `Class::alias`, the key
// built in `arena` as a nested class's is.
void RegisterClassTypeAliases(const RtlirDesign* design, SimContext& ctx,
                              Arena& arena);
// §6.18 with §8.3: the class's own typedefs naming a class the run already
// holds, bound under `Class::alias`; the rest wait for
// RegisterClassTypeAliases.
void RegisterClassScopeTypedefAliases(ClassTypeInfo* info, SimContext& ctx,
                                      Arena& arena);
// §16.8 and §16.12: the module's named sequence and property declarations,
// which an instance of one is expanded from at the run.
void RegisterModuleSequenceDecls(const RtlirModule* mod, SimContext& ctx);
void RegisterProcessClassType(SimContext& ctx, Arena& arena);

}  // namespace delta

#endif  // DELTA_SIMULATOR_LOWERER_REGISTER_H_
