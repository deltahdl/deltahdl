#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/types.h"
// GenBlockConsts, the §27.4 loop-index values a lowered thread carries.
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_primitives.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

class Arena;
class DiagEngine;
class SimContext;
struct ImportItem;
struct ModuleItem;
struct RtlirContAssign;
struct RtlirUdpInst;
struct PackageDecl;
struct RtlirDesign;
struct Expr;

// §16.9.11: a clock and the reads of `triggered` of one sequence in contexts
// on it, each by the sequence's name as the read writes it.
using ClockReads = std::pair<std::vector<EventExpr>, std::vector<const Expr*>>;
struct RtlirModule;
struct RtlirProcess;
struct ProceduralCheckerAssertion;
struct AssocArrayObject;
struct QueueObject;
struct ClassDecl;
struct ClassTypeInfo;
struct Expr;
struct RtlirModuleInst;
struct RtlirPortBinding;
struct RtlirVariable;
struct Variable;
struct Process;

// §4.4: puts a lowered process on the scheduler, as an evaluation event at
// time zero in the process's own region, so that it runs once when the
// simulation starts. Every kind of process is started this way -- the
// structured procedures of §9.2 and the continuous assignments of §10.3 alike
// -- which is why it is declared here rather than kept file-local:
// src/simulator/lowerer.cpp defines it and src/simulator/lowerer_contassign.cpp
// is its second caller.
void ScheduleProcess(Process* proc, SimContext& ctx);

// The timing one module instance declares -- §30.3's specify blocks and §28.4's
// gate instantiations -- with the instance they belong to. The prefix is what
// tells two instances of one cell apart, since §30.4 has a specify block name
// its terminals by the bare port names of the module it stands in and §29.8
// puts a gate instance inside a module the same way. It is recorded rather than
// acted on where it is found, because a module path delay or a gate delay may
// be written as a specparam and the specparam variables of every instance have
// to exist first.
struct SpecifyScope {
  std::string inst_prefix;
  const RtlirModule* module;
};

// The names one lowered process's concurrent assertion property and sampled
// value function calls read, with the instance prefix the process was lowered
// under. §16.5.1 samples a variable rather than reading it live, and which
// variable a name reaches is a question about the whole design: §23.6 lets the
// property name a variable of a child instance, whose storage does not exist
// until that instance is lowered. The names are therefore recorded where they
// are found and resolved once every module has been lowered, the way
// SpecifyScope defers a specify block for the specparams it may name.
struct AssertionSampleScope {
  std::string inst_prefix;
  std::vector<std::string> names;
};

class Lowerer {
 public:
  Lowerer(SimContext& ctx, Arena& arena, DiagEngine& diag);

  void Lower(const RtlirDesign* design);

 private:
  void LowerModule(const RtlirModule* mod);
  // A top-level module after the first, lowered as an instance of its own
  // name so its declarations are its own. Defined in lowerer_child.cpp.
  void LowerParallelTop(const RtlirModule* mod);
  void LowerParams(const RtlirModule* mod);
  // §6.20: the storage of the one parameter `p`, keyed under `full`, the name
  // the instance's processes read it by.
  void LowerParam(const RtlirParamDecl& p, std::string_view full);
  // §27.4 and §27.5 with §23.6: registers each RtlirGenBlockMember of `mod`
  // under the key its path spells below the instance inst_prefix_ names.
  // Defined in lowerer_gen_block_members.cpp.
  void RegisterGenBlockMembers(const RtlirModule* mod);
  // §10.11: joins the nets each alias statement of `mod` lists, under the
  // names the instance inst_prefix_ names creates them by. Defined in
  // src/simulator/lowerer_child.cpp beside the child lowering that shares it.
  void LowerAliases(const RtlirModule* mod);
  // Lowers the processes, continuous assignments, bidirectional switches and
  // UDP instances of `mod`; a program's or a checker's processes and
  // continuous assignments are scheduled in the Reactive region.
  void LowerModuleProcesses(const RtlirModule* mod);
  // §17.3: the event control of `proc`, each event formal of the checker
  // instance being lowered replaced by the event expression its actual is,
  // held as long as the process that waits on it. Defined in
  // src/simulator/lowerer_inst.cpp.
  const std::vector<EventExpr>& ClockOf(const RtlirProcess& proc);
  // Creates the storage a variable declaration states, keyed under `name`.
  // `name` is the name the storage is reachable by, which is the declared name
  // at the top of the hierarchy and the instance-prefixed form under an
  // instance; every property recorded here is recorded against it, so a
  // declaration states the same thing wherever in the hierarchy it sits. The
  // maps hold `name` rather than a copy, so a name built at run time must be
  // interned in the arena before it is passed.
  void LowerVar(std::string_view name, const RtlirVariable& var);
  void LowerVarInit(std::string_view name, const RtlirVariable& var,
                    Variable* v, uint32_t width);
  // §6.11.2/§6.12.1: applies the implicit conversions a declaration
  // initializer undergoes as an assignment to its declared variable.
  Logic4Vec CoerceVarInitValue(const RtlirVariable& var, Logic4Vec val,
                               uint32_t width);
  void LowerVarAggregate(std::string_view name, const RtlirVariable& var);
  void LowerProcesses(const std::vector<RtlirProcess>& procs, bool from_program,
                      uint32_t program_block_id);
  void LowerProcess(const RtlirProcess& proc, bool from_program,
                    uint32_t program_block_id);
  void InstallGenBlockConsts(const GenBlockConsts& consts, Process* p);
  void LowerContAssign(const RtlirContAssign& ca, bool from_program);
  // §28.8: links a bidirectional switch's two nets and starts the process
  // that follows its control. Defined in
  // src/simulator/lowerer_bidir_switch.cpp.
  void LowerBidirSwitch(const RtlirBidirSwitch& sw, bool from_program);
  // §29.8: creates the process that drives one user-defined primitive
  // instance's output terminal from the state table §29.3.4 defines.
  // `from_program` says the instance sits in a program, whose drives are
  // reactive (§24.3.1); LowerContAssign takes it for the same reason, since
  // §29.8 instantiates a UDP just as a gate is. Defined in
  // src/simulator/lowerer_udp.cpp.
  void LowerUdpInst(const RtlirUdpInst& inst, bool from_program);
  // §16.13.6 and §16.9.11: the monitor processes of a module's named
  // sequences and of the instances with arguments its bodies apply
  // `triggered` to. Defined in src/simulator/lowerer_sequence_monitors.cpp.
  void LowerSequenceMonitors(const RtlirModule* mod);
  // §16.9.3: a process for each value change function in `body` given a
  // clocking event of its own, recording its argument's sample at each tick
  // of that event (lowerer_sampled_clocks.cpp).
  void LowerSampledClockMonitors(const Stmt* body);
  // `context_clock`, where not null, is the clock of the context applying
  // `triggered` to the sequence, which a sequence declared without a clock
  // takes (§16.9.11).
  void LowerSequenceMonitor(const ModuleItem* seq, std::string_view ep_name,
                            const std::vector<EventExpr>* context_clock);
  // §16.9.11: the monitor of the named sequence `seq`, on `first_clock` where
  // it is declared without a clock, and, so declared, one more for each clock
  // of `further`, whose end point the reads grouped under that clock, `e` as
  // each writes it, take.
  void CreateEndPoint(std::string_view ep_name);
  void LowerFreeVariableSolver(const RtlirModule* mod);
  void LowerNamedSequenceMonitor(const ModuleItem* seq,
                                 const std::vector<EventExpr>* first_clock,
                                 const std::vector<ClockReads>& further);
  // Lowers `cls` and binds it under its bare name. `scope_items` are the items
  // of the scope the class is declared in -- the compilation unit's function
  // and task declarations, a package's items or a module's function
  // declarations -- which §8.24 has hold the class's out-of-block method
  // bodies; they are attached before the vtable is built so that a virtual
  // call of §8.20, through this class or one derived from it later, reaches
  // the body. Defined in src/simulator/lowerer_class.cpp.
  void LowerClassDecl(const ClassDecl* cls,
                      const std::vector<ModuleItem*>& scope_items);
  // The two halves of LowerClassDecl, for a scope whose variables the
  // class's static initializers may name: RegisterClassDecl builds and binds
  // the class as LowerClassDecl does, each static property at its zero
  // default, and InitClassStaticProperties then evaluates the static
  // initializers of `cls` and of the classes nested in it (§8.23) once, in a
  // frame of the scope declaring the class (§8.9, §6.21). LowerModule
  // registers a module's classes ahead of its variables, which a `C h =
  // new;` needs, and initializes their statics after them, which a `static
  // int s = K;` on the module's K needs. Defined in
  // src/simulator/lowerer_class.cpp.
  void RegisterClassDecl(const ClassDecl* cls,
                         const std::vector<ModuleItem*>& scope_items);
  void InitClassStaticProperties(const ClassDecl* cls);
  // §26.2: the package declaring `cls`, or empty for a class of a module or
  // the compilation unit. Defined in src/simulator/lowerer_class.cpp.
  std::string_view DeclaringPackage(const ClassDecl* cls) const;
  void LowerImports(const RtlirModule* mod);
  // §3.12.1: an import written in the compilation-unit scope makes the
  // package's names visible to every module of the unit, which reaches them
  // after searching its own scope. Applied once, ahead of the modules, from
  // the unit's own import declarations; §26.6's exports are already bound
  // (AliasPackageExports, run by LowerDesignData in lowerer_data_init.cpp
  // before the package initializers), each name a package exports keyed under
  // the exporting package to the declaring package's storage or subroutine.
  // Defined in lowerer_import.cpp.
  void LowerCompilationUnitImports();
  // The unit's own class declarations, after its imports
  // (InitCompilationUnitData) for the reason given at the definition. Defined
  // in lowerer.cpp.
  void LowerCompilationUnitClasses();
  // The three steps of the design's data, each defined in
  // src/simulator/lowerer_data_init.cpp with the order it keeps: the type
  // names and the packages' and the unit's storage, the packages'
  // initializers with them; then the unit's imports and its initializers;
  // then, once every class of the packages and the unit is lowered and ahead
  // of every module, the objects the two scopes' declaration assignments
  // construct.
  void LowerDesignData();
  void InitCompilationUnitData();
  void ConstructDesignData();
  // §26.3: `p::C` reaches a package's class whether or not the package was
  // imported, so every package class no import has lowered is lowered here and
  // bound under its qualified key, ahead of the modules (§26.2 has the
  // package's declaration assignments, which construct objects of them, made
  // before a module's) and displacing no unqualified binding an import or a
  // declaration made: a bare name nothing held is left unbound until the
  // modules are lowered and RebindStrayPackageClassNames binds it to the
  // class. Defined in lowerer_import.cpp.
  void LowerUnimportedPackageClasses();
  void LowerUnimportedClassesOf(const PackageDecl* pkg);
  void RebindStrayPackageClassNames();
  // Lowers the class `cls` that package `pkg` declares and binds it under
  // "pkg::name" as well as under the bare name LowerClassDecl gives it, once:
  // a second call for the same class finds the qualified key and does nothing,
  // so that the static properties of §8.9 have one copy however the class is
  // named. Defined in lowerer_import.cpp.
  void LowerPackageClass(const PackageDecl* pkg, const ClassDecl* cls);
  // §26.6: binds the class `cls` of package `pkg`, once lowered, under the
  // qualified key of every package whose exports hand it on, to the one
  // ClassTypeInfo the declaring package's key holds. Defined in
  // lowerer_import.cpp.
  void AliasExportedClassKeys(const PackageDecl* pkg, const ClassDecl* cls);
  void LowerPackageItem(const PackageDecl* pkg, ModuleItem* item);
  // §26.3: applies one import declaration, wildcard or explicit, to the scope
  // inst_prefix_ names; LowerImports and LowerCompilationUnitImports both go
  // through it. Defined in lowerer_import.cpp.
  void LowerOneImport(const ImportItem& imp);
  // The import declarations among a compilation unit's `items`, the explicit
  // ones first (§26.5), each through LowerOneImport.
  void LowerUnitImportItems(const std::vector<ModuleItem*>& items);
  PackageDecl* FindPackage(std::string_view name) const;

  void LowerImportedName(PackageDecl* pkg, std::string_view name,
                         std::unordered_set<const PackageDecl*>& visited);

  void LowerAllImported(PackageDecl* pkg,
                        std::unordered_set<const PackageDecl*>& visited);

  // §26.3: binds one imported parameter or variable of `pkg` under its
  // unqualified spelling in the scope whose imports are being lowered, which is
  // the instance inst_prefix_ names. The other two walk a whole package for a
  // wildcard import and one named item for an explicit one.
  void AliasPackageDataItem(const PackageDecl* pkg, const ModuleItem* item);
  void AliasAllPackageDataItems(const PackageDecl* pkg);
  void AliasNamedPackageDataItem(const PackageDecl* pkg,
                                 std::string_view item_name);
  // §26.3: binds an explicitly imported enumeration literal of `pkg`, which
  // is a constant of the package and not an item of it, under its unqualified
  // spelling in the same scope; answers false where `pkg` declares no
  // enumeration member of that name. Defined in lowerer_import.cpp.
  bool AliasPackageEnumMember(const PackageDecl* pkg, std::string_view name);
  // The binding the three above make: `name` in the scope inst_prefix_ names,
  // aliased to the package's own storage under `qname`, unless the scope has
  // already bound the name (§26.5). Defined in lowerer_import.cpp.
  void AliasImportedPackageName(std::string_view name, std::string_view qname);
  void LowerDynArrayInit(QueueObject* q, const RtlirVariable& var);
  void InitAssocDefault(const Expr* init, AssocArrayObject* aa);
  void RegisterEnumForCast(std::string_view name, const RtlirVariable& var);
  void RegisterEnumTypes(const RtlirModule* mod);
  // §6.19.5 with §6.20.2: records the enumeration each value parameter of
  // `mod` was declared with, under the key its storage stands under, so an
  // enum method on the parameter's name finds it. Called once the module's
  // enumerations are registered.
  void RegisterParamEnumTypes(const RtlirModule* mod);
  // Records that `mod` declares specify blocks or gate instances, under the
  // instance prefix in force when it is called, so that Lower can register them
  // once every module has been lowered. A module declaring neither is not
  // recorded; either alone is enough.
  void RecordSpecifyScope(const RtlirModule* mod);
  // Records the variable names one process's property and sampled value
  // function calls read, under the instance prefix in force, so that Lower can
  // enrol them for §16.5.1 sampling once every module has been lowered. A
  // process reading none is not recorded.
  void RecordAssertionSampleScope(const RtlirProcess& proc);
  // The same for one statement, a process's body or a statement of a task
  // or function body, which §16.17 has hold an expect statement whose
  // property reads sampled values as a concurrent assertion's does.
  void RecordAssertionSampleScope(const Stmt* body);
  // Records the names the tasks and functions of `mod` read in expect
  // statements and sampled value function calls.
  void RecordSubroutineAssertionSampleScopes(const RtlirModule* mod);
  // Enrols into the run's AssertionSampleStore every variable
  // RecordAssertionSampleScope gathered, once every module has been lowered.
  void RegisterDesignAssertionSampling();
  // Registers into the run's SpecifyManager everything RecordSpecifyScope
  // gathered, once every module has been lowered.
  void RegisterDesignTiming();
  // §17.3: where `proc` is a static assertion of a procedural checker
  // instance, or of a checker nested in one, it is kept for the procedure
  // instantiating the instance to queue rather than lowered as a process;
  // answers whether it was.
  bool KeepProceduralCheckerAssertion(const RtlirProcess& proc);
  // §17.3 with §16.14.6.1: where `inst`, lowered under inst_prefix_, is a
  // procedural checker instance, records under its prefix `child_prefix` the
  // actuals ProceduralActualInInstantiatingScope rewrites, for its
  // assertions to read in their formals' place, and enrols the names they
  // read as sampled.
  void RecordProceduralCheckerActuals(const RtlirModuleInst& inst,
                                      const std::string& child_prefix);
  // §17.3: records the checker instantiations `proc`, lowered as `p`, holds,
  // each with the instance it names.
  void RecordCheckerInstantiations(const RtlirProcess& proc, Process* p);
  // §17.3: gives each process the assertions of the instances its checker
  // instantiations name, once every instance has been lowered.
  void LinkCheckerInstantiations();
  // §17.3: lowers the body of the child instance `child`, whose prefix is
  // inst_prefix_, as a procedural checker root where it is a procedural
  // checker instance outside any other.
  void LowerChildBodyUnderCheckerRoot(const RtlirModuleInst& child);
  void LowerChildModules(const RtlirModule* mod);
  void RegisterChildInstanceKeys(const RtlirModule* mod);
  // One instance of LowerChildModules: its module's declarations, port
  // connections, processes and instances, all under the instance's name
  // joined to inst_prefix_.
  void LowerChildInstance(const RtlirModuleInst& child);
  // The part of LowerChildInstance that follows the port connections: the
  // instance's aliases, processes, assignments, primitives, clocking blocks
  // and instances, under the prefix inst_prefix_ holds.
  void LowerChildBody(const RtlirModule* mod);
  // §14.3: registers the module's clocking blocks with the run's
  // ClockingManager and creates the event variable §14.10 triggers under each
  // block's name. Defined in src/simulator/lowerer_clocking.cpp.
  void LowerClockingBlocks(const RtlirModule* mod);
  // §14.3: arms every registered block's clock watcher, once every module has
  // been lowered and each block's clock variable exists.
  void AttachDesignClocking();
  void CreateChildModuleVariables(const std::string& inst_prefix,
                                  const RtlirModule* resolved);

  void LowerPortBindings(const RtlirModuleInst& inst, bool from_program);
  void RecordCheckerActualSampleScope(const RtlirModuleInst& inst);
  bool LowerArrayPortBinding(const RtlirModuleInst& inst,
                             const RtlirPortBinding& binding,
                             const std::string& inst_seg, bool from_program);
  bool TryAliasInterfacePort(const RtlirModuleInst& inst,
                             const RtlirPortBinding& binding);
  std::string ConnectedInstanceKey(std::string_view name) const;
  const RtlirModule* ConnectedInterface(const RtlirPort& port, const Expr* conn,
                                        const Expr*& instance) const;
  void RegisterModportExpressions(const RtlirPort& port, const Expr* conn,
                                  const RtlirModule* ifc,
                                  const std::string& port_key,
                                  const std::string& instance_key);
  void RegisterExportedSubroutines(const RtlirModuleInst& inst,
                                   std::string_view port_name,
                                   const RtlirModule* ifc,
                                   const std::string& instance_key);

  SimContext& ctx_;
  Arena& arena_;
  const RtlirDesign* design_ = nullptr;
  uint32_t next_id_ = 0;
  uint32_t next_program_block_id_ = 1;
  std::string inst_prefix_;
  // The module whose imports LowerImports is lowering, so that
  // AliasImportedPackageName can leave a name the module declares to the
  // declaration (§26.5); null outside LowerImports, where the compilation
  // unit's imports bind every name.
  const RtlirModule* importing_module_ = nullptr;
  // The prefix of the generate block whose import LowerImports is lowering
  // (RtlirImport::scope_prefix), between the instance prefix and the name in
  // the key AliasImportedPackageName binds; empty for a module's own import.
  std::string_view import_scope_prefix_;
  std::vector<SpecifyScope> specify_scopes_;
  std::vector<AssertionSampleScope> assertion_sample_scopes_;
  // §17.5: the processes being lowered are a checker's, whose always_ff
  // procedures read sampled values.
  bool lowering_checker_ = false;
  // §17.3: the prefix of the procedural checker instance being lowered, the
  // outermost one where checkers nest, and empty outside one.
  std::string procedural_checker_root_;
  // §17.3: the actuals RecordProceduralCheckerActuals recorded, under the
  // prefix of their procedural checker instance.
  std::unordered_map<std::string, ActualsByFormal> procedural_checker_actuals_;
  // §17.3: the static assertions kept by KeepProceduralCheckerAssertion,
  // under the prefix of their procedural checker instance.
  std::unordered_map<std::string,
                     std::vector<const ProceduralCheckerAssertion*>>
      procedural_checker_assertions_;
  // §17.3: each process holding a checker instantiation, with the statement
  // and the prefix of the instance it names, for LinkCheckerInstantiations.
  struct CheckerInstantiationLink {
    Process* process = nullptr;
    const Stmt* stmt = nullptr;
    std::string inst_prefix;
  };
  std::vector<CheckerInstantiationLink> checker_instantiation_links_;
  // §25.9: the prefix of each interface instance, whose variables a virtual
  // interface can reach whatever name the reading expression spells.
  std::vector<std::string> interface_instance_prefixes_;
  void EnrollInterfaceMembers(std::string_view name,
                              const std::string& scope_prefix);
  void EnrollArrayElements(const std::string& name);
  // The instance output ports whose connection carries their module path
  // delays (RtlirContAssign::module_path_port), so that an assignment inside
  // the instance driving one of them does not carry them a second time.
  // LowerPortBindings fills it before the instance's own body is lowered.
  std::unordered_set<std::string> path_delayed_ports_;
  // The bare class names LowerUnimportedPackageClasses found no scope had
  // bound, each with the package class the pass bound it to, which
  // RebindStrayPackageClassNames binds again once the modules are lowered.
  std::vector<std::pair<std::string_view, ClassTypeInfo*>>
      stray_package_class_names_;
};

}  // namespace delta
