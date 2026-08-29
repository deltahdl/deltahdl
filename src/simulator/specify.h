#pragma once

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/specify_sdf.h"

namespace delta {

class SimContext;
class Scheduler;

// §32.4.3: a module path declaration together with the module instance it was
// registered under. SpecifyManager::RebuildPathDelaysForSpecparam recomputes a
// path from its declaration when an SDF LABEL changes a specparam that path's
// delay expression reads, and the rebuilt path has to be filed back at the
// instance the declaration came from. §30.4 has a module path name its
// terminals by the declaring module's own port names, so the declaration alone
// spells a path identically for every instance of the cell: a rebuild left at
// the empty prefix is filed beside the declared path rather than replacing it,
// SpecifyManager::AddPathDelay comparing PathDelay::inst_prefix.
struct RegisteredPathDecl {
  const SpecifyPathDecl* decl = nullptr;
  std::string inst_prefix;
};

// §32.4.3: a system timing check declaration together with the module instance
// it was registered under. SpecifyManager::RebuildTimingChecksForSpecparam
// recomputes a check's constraint limits from its declaration when an SDF LABEL
// changes a specparam one of those limit expressions reads, and the rebuilt
// check has to be filed back at the instance the declaration came from. §31.2
// puts a system timing check inside a specify block and §30.3 puts that block
// inside a module declaration, and §31.3 has the check name its reference and
// data signals by the declaring module's own port names, so the declaration
// alone spells a check identically for every instance of the cell: a rebuild
// left at the empty prefix replaces whichever instance's check stands first,
// SpecifyManager::AddTimingCheck comparing TimingCheckEntry::inst_prefix. The
// prefix is also what the limit expressions are evaluated under, a constraint
// limit written as a specparam being read by its bare name.
struct RegisteredTimingCheckDecl {
  const TimingCheckDecl* decl = nullptr;
  std::string inst_prefix;
};

// §32.4.3: a gate instantiation together with the module instance it was
// registered under. SpecifyManager::RebuildGateDriversForSpecparam recomputes a
// gate's propagation delays from its declaration when an SDF LABEL changes a
// specparam that delay expression reads, and the rebuilt drivers have to be
// filed back at the instance the declaration came from. §29.8 puts a primitive
// instance inside a module the way §30.3 puts a specify block there, and §28.4
// has a gate name its terminals by the declaring module's own port names, so
// the declaration alone spells an output identically for every instance of the
// cell: a rebuild left at the empty prefix overwrites whichever instance's
// driver stands first, SpecifyManager::ReplacePrimitiveDriver comparing
// PrimitiveDriver::inst_prefix. The prefix is also what the delay expression is
// evaluated under, a gate delay written as a specparam being read by its bare
// name.
struct RegisteredGateDecl {
  const ModuleItem* gate = nullptr;
  std::string inst_prefix;
};

// §32.4.3: a specparam the design declared, together with the module instance
// that declared it. An SDF LABEL annotates to specparams, so the manager has to
// know which names are specparams at all. §30.3 has a specify block declare its
// specparams by bare names, so two instances of one cell declare a specparam
// spelled identically, and Lowerer::CreateChildModuleVariables keys an
// instantiated module's specparam under that instance's hierarchical prefix.
// SpecifyManager::ApplyAnnotatedSpecparam joins the two fields back into the
// dotted name SimContext::FindVariable reads the storage out of.
struct DeclaredSpecparam {
  std::string inst_prefix;
  std::string name;
};

class SpecifyManager {
 public:
  void AddPathDelay(PathDelay delay, bool preserve_pulse_limits = false);

  // §32.4.3 (delay expression per §30.5): add a module path from its
  // declaration and hold on to the declaration. Keeping it is what lets the
  // path's delay be recomputed from its own expression later; a path whose
  // delay expression reads a specparam has to follow that specparam when an SDF
  // LABEL changes it, rather than staying at the value the predecessor
  // produced.
  //
  // Pass `default_pulse_limits` when the declaration is a design's own. §30.7
  // states that by default both the error limit and the reject limit are set
  // equal to the delay, so the flag applies InitDefaultPulseLimits (declared in
  // simulator/specify_path_delay.h) to the built path. That is the state a
  // PATHPULSE$ specparam (§30.7.1), a global pulse limit invocation option
  // (§30.7.2) or an SDF pulse limit (§30.7.3) then replaces. A caller whose
  // subject is the delay alone leaves the flag off, and the path's two limits
  // stay at zero.
  //
  // `inst_prefix` is the hierarchical prefix of the module instance whose
  // specify block holds `decl`, ending in a `.` and empty for a module
  // elaborated as a top. §30.4 has a module path name its terminals by the
  // declaring module's own port names, so two instances of one cell declare
  // paths spelled identically and the prefix is what tells them apart. It is
  // stamped onto PathDelay::inst_prefix before AddPathDelay files the path.
  void AddPathDelayFromDecl(const SpecifyPathDecl& decl, SimContext& ctx,
                            Arena& arena, bool default_pulse_limits = false,
                            std::string_view inst_prefix = {});

  // §32.4.1: apply one SDF delay entry to the module paths already declared.
  // A nonconditional entry reaches every path between the two ports it names;
  // a conditional or ifnone entry may reach only a path between those same two
  // ports carrying that same condition, and lands nowhere when the module
  // declares no such path rather than inventing one. Returns whether it landed
  // on a declared path. This is the backannotation counterpart of AddPathDelay,
  // which is how a declaration enters the manager in the first place.
  //
  // Like AddPathDelay, this matches on PathDelay::inst_prefix as well as the
  // port pair. SdfCellInstancePrefix in simulator/sdf_annotate.cpp derives that
  // prefix from the cell's own instance path, taken relative to the §32.9
  // module_instance operand, so an SDF record reaches the instance it names and
  // no other. CellInScope filters whole cells before any path is reached and is
  // the coarser half of the same question.
  bool AnnotateSdfPathDelay(PathDelay delay,
                            PathDelayPulseRetention retain = {});

  // §32.4.1: the incremental form of the same rule -- the entry's values add to
  // what the path already carries instead of replacing it, and a conditional
  // entry is restricted to declared paths in exactly the same way.
  bool IncrementSdfPathDelay(const PathDelay& delta);

  void AddTimingCheck(TimingCheckEntry check);

  // Applies one SDF timing check annotation to every declared check it matches.
  // Returns whether it matched anything, so the caller can tell placed data
  // apart from data that found no home (§32.3 requires a warning for the
  // latter).
  //
  // `inst_prefix` is the module instance the annotation reaches, in the
  // spelling TimingCheckEntry::inst_prefix carries, and it is matched exactly:
  // the annotation reaches the checks of that instance and of no other. An
  // empty prefix names the module the design was elaborated as, which is the
  // prefix a check declared in that module carries; it is not a wildcard.
  // §31.2 puts a system timing check inside a specify block, so two instances
  // of one cell declare checks naming identically spelled signals and the
  // instance is what tells them apart.
  //
  // The annotation's edge and condition stay permissive where its instance does
  // not, because §32.4.2 rules that an SDF check naming no edge and no
  // condition matches every corresponding declared check. No such unspecified
  // instance exists: SdfCellInstancePrefix (simulator/sdf_parser.h) answers a
  // definite prefix for every cell, so an empty value stands for the root
  // rather than for an instance the file left out.
  bool AnnotateSdfTimingCheck(const SdfTcAnnotation& annotation,
                              std::string_view inst_prefix = {});

  // §32.4.1: register a module output driven by a gate primitive, so a DEVICE
  // delay that finds no specify path for that output can still land on it.
  void AddPrimitiveDriver(PrimitiveDriver driver);

  // §32.4.3 (drivers per §32.4.1): register every module-output driver one gate
  // instantiation contributes, keeping the gate declaration so its propagation
  // delay expression can be recomputed if an SDF LABEL changes a specparam that
  // expression reads.
  //
  // `inst_prefix` is the hierarchical prefix of the module instance the gate
  // was instantiated in, ending in a `.`, and is empty for a module elaborated
  // as a top. §28.4 has a gate instantiation name its terminals by the
  // declaring module's own port names, so two instances of one cell drive
  // outputs spelled identically; the prefix is recorded on each driver as
  // PrimitiveDriver::inst_prefix, which is what tells the two instances apart.
  // It travels with the kept declaration as well, as RegisteredGateDecl above,
  // because RebuildGateDriversForSpecparam files a rebuilt driver back at the
  // instance the declaration came from. It defaults to the empty prefix so a
  // caller registering the gates of one module can name the gate alone.
  void AddPrimitiveDriversFromGate(const ModuleItem& gate, SimContext& ctx,
                                   Arena& arena,
                                   std::string_view inst_prefix = {});

  const std::vector<PrimitiveDriver>& GetPrimitiveDrivers() const {
    return primitive_drivers_;
  }

  // §32.4.1 Table 32-1: apply one SDF DEVICE delay. With no operand it reaches
  // every specify path to a module output; with an operand naming a module
  // output it reaches only the paths ending at that output; any other operand
  // names a module instance, whose outputs are the ones declared here. When the
  // targeted outputs have no specify path at all, the delay lands instead on
  // the primitives driving them. Returns whether it reached anything, so the
  // caller can warn about data that found no home (§32.3).
  //
  // `inst_prefix` is the prefix of the instance the entry's CELLINSTANCE named,
  // in the form PathDelay::inst_prefix carries. §30.4 names a path's terminals
  // by the declaring module's own port names, so two instances of one cell hold
  // outputs spelled identically and the prefix is what keeps the delay off the
  // outputs of the instance the entry did not name.
  bool AnnotateSdfDeviceDelay(const SdfDeviceAnnotation& annotation,
                              std::string_view inst_prefix);

  void AnnotateSdf(SdfAnnotation annotation);

  // §32.4.3: apply one LABEL entry's value to the specparam it names. The value
  // the file asked for is recorded whatever the name turns out to be, and the
  // design's own storage is written only when that name is a specparam the
  // design declared.
  //
  // `inst_prefix` is the hierarchical prefix of the module instance whose CELL
  // record the entry stood in, ending in a `.` and empty for a module
  // elaborated as a top; §32.5's CELLINSTANCE is what names that instance.
  // §30.3 has a specify block declare its specparams by bare names, so two
  // instances of one cell declare a specparam spelled identically and the
  // prefix is what keeps the annotation off the other instance's.
  void SetSpecparamValue(SpecparamValue spec,
                         std::string_view inst_prefix = {});

  // §32.4.3, the INCREMENT form: the entry's value adds to what the specparam
  // already carries. `inst_prefix` names the instance exactly as it does for
  // SetSpecparamValue, so two instances of one cell accumulate separately.
  void IncrementSpecparamValue(SpecparamValue delta,
                               std::string_view inst_prefix = {});
  void AddInterconnectDelay(InterconnectDelay delay);

  void IncrementInterconnectDelay(const InterconnectDelay& delta);

  // §32.4.4: hand the manager the design's interconnect connectivity. An
  // interconnect delay is annotated between module ports of the design rather
  // than onto a declaration, so without this the annotator has no ports, nets
  // or primitives to look an entry's names up in.
  void BindDesignInterconnect(InterconnectTopology topology);

  const InterconnectTopology& GetInterconnectTopology() const {
    return topology_;
  }

  // §32.4.4 Table 32-3: apply one INTERCONNECT, PORT or NETDELAY entry. A PORT
  // entry annotates the delay from all sources to the port it names; a NETDELAY
  // entry does the same for a port, or for every load port on the net it names;
  // an INTERCONNECT entry annotates the delay for one source/load pair, and
  // warns but still annotates the load when its source is not found or is not
  // on the load's net. An entry naming a primitive pin annotates nothing, since
  // interconnect delays go only between module ports.
  SdfInterconnectOutcome AnnotateSdfInterconnect(
      const SdfInterconnectAnnotation& annotation);

 private:
  // §32.4.4: the three entry constructs, and the load/source resolution an
  // INTERCONNECT entry needs before its delay can be placed.
  SdfInterconnectOutcome AnnotateSdfPortDelay(
      const SdfInterconnectAnnotation& annotation,
      const std::string& load_name);
  SdfInterconnectOutcome AnnotateSdfNetDelay(
      const SdfInterconnectAnnotation& annotation,
      const std::string& load_name);
  SdfInterconnectOutcome AnnotateSdfInterconnectPath(
      const SdfInterconnectAnnotation& annotation, const std::string& load_name,
      const std::string& source_name);
  std::vector<const InterconnectTerminal*> ResolveInterconnectLoadPorts(
      const std::string& load_name, SdfInterconnectOutcome& out);
  const InterconnectTerminal* ResolveInterconnectSourcePort(
      const std::string& source_name, SdfInterconnectOutcome& out) const;
  std::vector<std::string> CoveredSourcesOnSameNet(
      const InterconnectTerminal* source,
      const InterconnectTerminal* first_load) const;
  std::vector<std::string> CoveredSourcesOffNet(
      const InterconnectTerminal* source, const std::string& source_name,
      const std::string& load_name, const InterconnectTerminal* first_load,
      SdfInterconnectOutcome& out) const;
  void ExtendLoadsUpHierarchy(
      const InterconnectTerminal* source,
      std::vector<const InterconnectTerminal*>& loads) const;
  std::string InterconnectNetIdOf(std::string_view name) const;
  bool DelayLoadCoversReference(const InterconnectDelay& delay,
                                const std::string& net_id,
                                std::string_view name) const;

 public:
  // §32.4.4: the annotated delay from `source` to `load`, or null when nothing
  // is annotated between them. A delay recorded as being from all sources
  // answers for any source, and a down-hierarchy annotation answers for every
  // source at or above the one the entry named.
  const InterconnectDelay* FindInterconnectDelay(std::string_view source,
                                                 std::string_view load) const;

  // §32.4.4: which value a reference to `name` reads. A reference to an
  // annotated load, or to anything hierarchically after it, reads the delayed
  // signal value and so reports the delay it sees; a reference to the source or
  // to any point on the net before the load reads the undelayed value.
  InterconnectReferenceRead ReadInterconnectReference(
      std::string_view name) const;

  // §32.4.4: start the annotated interconnect delays running in `ctx`. Each
  // annotated load follows its source's storage, and a transition of that
  // source is scheduled to arrive at the load the annotated delay later, with
  // the transition's own slot of the twelve choosing the delay. The arrivals
  // are recorded in order, so what the load saw and when is observable after
  // the run.
  void StartInterconnectPropagation(SimContext& ctx, Scheduler& scheduler);

  const std::vector<InterconnectArrival>& GetInterconnectArrivals() const {
    return interconnect_arrivals_;
  }

  void RegisterSpecparamReevaluation(std::string name,
                                     std::function<void(uint64_t)> reevaluate);

  // §32.4.3: bind the manager to a running design's specparams. `names` are the
  // specparams one scope declared -- an SDF LABEL annotates to specparams, so a
  // LABEL entry naming anything else must not disturb the design -- and `ctx`
  // is where the design reads their values from. Writing the annotated value
  // there is what makes every later evaluation of an expression containing that
  // specparam, a procedural delay control among them, use the annotated value.
  //
  // `inst_prefix` is the hierarchical prefix of the module instance that
  // declared `names`, ending in a `.` and empty for a module elaborated as a
  // top. The names are added to what earlier calls bound rather than replacing
  // it: RegisterSpecifyBlocks calls this once per module instance that declared
  // a specify block, and replacing would leave only the last instance's
  // specparams annotatable.
  void BindDesignSpecparams(std::vector<std::string> names, SimContext& ctx,
                            Arena& arena, std::string_view inst_prefix = {});

  const std::vector<DeclaredSpecparam>& GetDeclaredSpecparamsWithInstance()
      const {
    return declared_specparams_;
  }

  // The declared specparam names alone, in the order they were bound. §30.3 has
  // a cell name its specparams by bare names, so one name here can stand for a
  // declaration in more than one instance; GetDeclaredSpecparamsWithInstance is
  // what tells those apart.
  std::vector<std::string> GetDeclaredSpecparams() const {
    std::vector<std::string> names;
    names.reserve(declared_specparams_.size());
    for (const auto& declared : declared_specparams_) {
      names.push_back(declared.name);
    }
    return names;
  }

  // §32.7: apply one SDF pulse-limit construct to the module paths it names in
  // the instance `inst_prefix` names. The construct reaches the two limits
  // alone and never the path's delay. Its values either state the limits or, in
  // INCREMENT mode, state amounts to change them by, where an amount that would
  // carry a limit below zero leaves it at zero. Either way a limit the
  // construct puts above the path's delay behaves as one put at the delay.
  //
  // `inst_prefix` is in the form PathDelay::inst_prefix carries, since §30.4
  // has two instances of one cell declare paths spelled identically.
  void AddSdfPulseLimit(const SdfPulseLimitSpec& spec,
                        std::string_view inst_prefix);

  // §30.7.1: apply the specify block's PATHPULSE$ pulse-control specparams to
  // the module's path delays. A non-path-specific specparam sets the limits of
  // every path; a path-specific specparam overrides only the path it names and
  // takes precedence over any non-path-specific one, regardless of the order in
  // which the specparams were declared.
  void ApplyPathSpecificPulseControl(const PulseControlSpecparam& s);
  void ResolvePulseControlSpecparams(
      const std::vector<PulseControlSpecparam>& specs);

  // §32.7: add the two amounts to the pulse limits of the module paths between
  // `src` and `dst` in the instance `inst_prefix` names, that prefix being in
  // the form PathDelay::inst_prefix carries. An annotation that lowers a limit
  // writes its amount as a negative number, so both are signed, and a limit the
  // addition would carry below zero is left at zero instead. An amount of zero
  // names a limit the annotation is not changing at all.
  void IncrementSdfPulseLimit(std::string_view src, std::string_view dst,
                              int64_t reject_delta, int64_t error_delta,
                              std::string_view inst_prefix);

  void SetGlobalPulseLimitPercents(uint8_t reject_pct, uint8_t error_pct);

  uint8_t RejectPulseLimitPercent() const { return reject_pulse_pct_; }
  uint8_t ErrorPulseLimitPercent() const { return error_pulse_pct_; }

  // §30.7.4.1: record the pulse-filtering style a specify block pulsestyle
  // declaration selects for a module path output.
  void SetPathOutputPulseStyle(std::string output, PulseStyle style);

  // §30.7.4.1: select a pulse-filtering style globally through the on-event/
  // on-detect invocation option. It takes precedence over any specify block
  // pulse style declaration.
  void SetGlobalPulseStyle(PulseStyle style);

  // §30.7.4.1: resolve the effective pulse-filtering style for a module path
  // output. A global invocation-option style wins over a specify block
  // declaration; absent both, the default is on-event. `output` is the module
  // path destination qualified by the instance prefix of the module that
  // declared the style, so two instances of one cell do not share a style.
  PulseStyle ResolvePulseStyle(std::string_view output) const;

  // §30.7.4.2: record the showcancelled mode a specify block showcancelled/
  // noshowcancelled declaration selects for a module path output.
  void SetPathOutputShowCancelled(std::string output, ShowCancelled mode);

  // §30.7.4.2: select a showcancelled mode globally through the showcancelled/
  // noshowcancelled invocation option. It takes precedence over any specify
  // block showcancelled declaration.
  void SetGlobalShowCancelled(ShowCancelled mode);

  // §30.7.4.2: resolve the effective showcancelled mode for a module path
  // output. A global invocation-option mode wins over a specify block
  // declaration; absent both, the default is noshowcancelled. `output` is the
  // module path destination qualified by the instance prefix of the module that
  // declared the mode, so two instances of one cell do not share a mode.
  ShowCancelled ResolveShowCancelled(std::string_view output) const;

  // §31.9.4: select the negative-timing-check and all-timing-checks-off
  // invocation options that govern this module's $setuphold/$recrem checks. The
  // selection is applied to the checks already registered as well.
  void SetTimingCheckInvocationOptions(TimingCheckInvocationOptions options);

  // §31.9.4: bring every registered check under the options currently in force.
  // A check that carries negative values loses its negative-value handling
  // unless the enabling option is active, no matter whether those values came
  // from its declaration or were annotated onto it afterwards.
  void ApplyTimingCheckInvocationOptions();

  const TimingCheckInvocationOptions& GetTimingCheckInvocationOptions() const {
    return timing_check_options_;
  }

  // §31.9.4: add a $setuphold/$recrem check from its parsed declaration, built
  // under the invocation options currently in force. The declaration is kept
  // (§32.4.3) so a limit expression that reads a specparam can be recomputed
  // when an SDF LABEL changes that specparam.
  //
  // `inst_prefix` is the hierarchical prefix of the module instance whose
  // specify block declared the check, ending in a `.` and empty for a module
  // elaborated as a top. §31.2 puts a system timing check inside a specify
  // block and §30.3 puts that block inside a module declaration, so two
  // instances of one cell declare checks naming identically spelled signals;
  // the prefix is recorded as TimingCheckEntry::inst_prefix, which is what
  // tells the two apart. It travels with the kept declaration as well, as
  // RegisteredTimingCheckDecl above, because RebuildTimingChecksForSpecparam
  // evaluates the limits in, and files the rebuilt check back at, the instance
  // the declaration came from. It defaults to the empty prefix so a caller
  // registering the checks of one module can name the declaration alone.
  void AddTimingCheckUnderOptions(const TimingCheckDecl& decl, SimContext& ctx,
                                  Arena& arena,
                                  std::string_view inst_prefix = {});

  const std::vector<SpecparamValue>& GetSpecparamValues() const {
    return specparam_values_;
  }
  const std::vector<InterconnectDelay>& GetInterconnectDelays() const {
    return interconnect_delays_;
  }

  uint64_t GetPathDelay(std::string_view src, std::string_view dst) const;
  const std::vector<PathDelay>& GetPathDelays() const { return path_delays_; }

  const std::vector<TimingCheckEntry>& GetTimingChecks() const {
    return timing_checks_;
  }

  const std::vector<SdfAnnotation>& GetSdfAnnotations() const {
    return sdf_annotations_;
  }

  bool HasPathDelay(std::string_view src, std::string_view dst) const;
  bool CheckSetupViolation(std::string_view ref, uint64_t ref_time,
                           std::string_view data, uint64_t data_time) const;
  bool CheckHoldViolation(std::string_view ref, uint64_t ref_time,
                          std::string_view data, uint64_t data_time) const;

  bool CheckSetupholdViolation(std::string_view ref, uint64_t ref_time,
                               std::string_view data, uint64_t data_time) const;

  bool CheckRemovalViolation(std::string_view ref, uint64_t ref_time,
                             std::string_view data, uint64_t data_time) const;

  bool CheckRecoveryViolation(std::string_view ref, uint64_t ref_time,
                              std::string_view data, uint64_t data_time) const;

  bool CheckRecremViolation(std::string_view ref, uint64_t ref_time,
                            std::string_view data, uint64_t data_time) const;

  bool CheckSkewViolation(std::string_view ref, uint64_t ref_time,
                          std::string_view data, uint64_t data_time) const;

  bool CheckTimeskewViolation(std::string_view ref, uint64_t ref_time,
                              std::string_view data, uint64_t data_time) const;

  bool CheckFullskewViolation(std::string_view ref, uint64_t ref_time,
                              std::string_view data, uint64_t data_time) const;

  bool CheckWidthViolation(std::string_view ref, uint64_t ref_time,
                           uint64_t data_time) const;

  bool CheckPeriodViolation(std::string_view ref, uint64_t ref_time,
                            uint64_t data_time) const;

  bool CheckNochangeViolation(std::string_view ref, uint64_t leading_ref_time,
                              uint64_t trailing_ref_time, std::string_view data,
                              uint64_t data_time) const;

  uint32_t PathDelayCount() const {
    return static_cast<uint32_t>(path_delays_.size());
  }
  uint32_t TimingCheckCount() const {
    return static_cast<uint32_t>(timing_checks_.size());
  }

 private:
  // §32.4.3: put one annotated specparam value where the design reads it, then
  // reevaluate the expressions that read it. Called from both the absolute and
  // the incremental form of a LABEL annotation, since both change the value.
  // `inst_prefix` names the instance the entry's CELL record stood in.
  // Lowerer::CreateChildModuleVariables keys an instantiated module's specparam
  // under that prefix, so `inst_prefix + name` is the key the storage is filed
  // under and the bare name reaches it only for a module elaborated as a top.
  void ApplyAnnotatedSpecparam(std::string_view inst_prefix,
                               const std::string& name, uint64_t value);
  // §32.4.3: recompute from their declarations the module path delays that read
  // a changed specparam. Only the paths declared in the instance `inst_prefix`
  // names are considered, a specparam of one instance not being the one an
  // identical declaration in another instance reads, and each rebuilt path is
  // filed back at that same instance.
  void RebuildPathDelaysForSpecparam(std::string_view inst_prefix,
                                     const std::vector<std::string>& changed);
  // §32.4.3: the same recomputation for the constraint limits of a timing
  // check, held to an instance the way RebuildPathDelaysForSpecparam is. Only
  // the checks declared in the instance `inst_prefix` names are considered, a
  // specparam of one instance not being the one an identical declaration in
  // another instance reads, and each rebuilt check is filed back at that same
  // instance.
  void RebuildTimingChecksForSpecparam(std::string_view inst_prefix,
                                       const std::vector<std::string>& changed);
  // §32.4.3: the same recomputation for the propagation delays of a gate
  // primitive, held to an instance the way RebuildPathDelaysForSpecparam is.
  // Only the gates registered in the instance `inst_prefix` names are
  // considered, a specparam of one instance not being the one an identical
  // declaration in another instance reads, and each rebuilt driver is filed
  // back at that same instance.
  void RebuildGateDriversForSpecparam(std::string_view inst_prefix,
                                      const std::vector<std::string>& changed);
  // §32.4.3: overwrite the driver already recorded for `rebuilt`'s output port
  // in `rebuilt`'s instance. §29.8 puts a primitive instance inside a module,
  // so the output port alone does not name one driver and the instance is
  // compared as well.
  void ReplacePrimitiveDriver(PrimitiveDriver rebuilt);

  // §32.4.3: is `name`, read in the instance `inst_prefix` names, a specparam
  // the design declared there? A LABEL entry naming anything else annotates
  // nothing.
  bool IsDeclaredSpecparam(std::string_view inst_prefix,
                           std::string_view name) const;

  // §32.4.4: place one already-resolved (source, load) pair's delay, either
  // replacing what is there or adding to it for an INCREMENT section.
  void PlaceInterconnectDelay(const SdfInterconnectAnnotation& annotation,
                              const std::string& source,
                              const std::string& load,
                              std::vector<std::string> covered_sources);

  // §32.4.4: sample every annotated source once and schedule the arrivals its
  // transitions cause. Run after each time step, which is what turns an
  // annotated delay into a delayed load-side value during a simulation.
  void PollInterconnectSources();

  std::vector<PathDelay> path_delays_;
  std::vector<PrimitiveDriver> primitive_drivers_;
  std::vector<TimingCheckEntry> timing_checks_;
  std::vector<SdfAnnotation> sdf_annotations_;

  // §32.4.3: what each LABEL entry asked for, kept whether or not the design
  // declared the name as a specparam. The index is keyed by the entry's name
  // qualified with the instance prefix of the CELL record it stood in, §30.3
  // having two instances of one cell declare a specparam spelled identically:
  // an INCREMENT entry in one instance's record must not add onto the value
  // another instance's record set.
  std::vector<SpecparamValue> specparam_values_;
  std::unordered_map<std::string, size_t> specparam_index_;
  std::vector<InterconnectDelay> interconnect_delays_;

  // §32.4.4: the design's interconnect connectivity, and the running side of an
  // annotated delay -- where each annotated source's value was last seen and
  // every arrival its transitions produced at the loads.
  InterconnectTopology topology_;
  SimContext* interconnect_ctx_ = nullptr;
  Scheduler* interconnect_scheduler_ = nullptr;
  std::unordered_map<std::string, uint64_t> interconnect_last_source_value_;
  std::vector<InterconnectArrival> interconnect_arrivals_;

  std::vector<std::pair<std::string, std::function<void(uint64_t)>>>
      specparam_reevaluators_;

  // §32.4.3: the design side of a LABEL annotation -- the specparams the
  // design's scopes declared, each with the instance that declared it, the
  // context and arena their values live in, and the module path and gate
  // declarations kept so their delay expressions can be reevaluated, each
  // likewise with the instance it was registered under.
  std::vector<DeclaredSpecparam> declared_specparams_;
  SimContext* specparam_ctx_ = nullptr;
  Arena* specparam_arena_ = nullptr;
  std::vector<RegisteredPathDecl> path_decls_;
  std::vector<RegisteredTimingCheckDecl> timing_check_decls_;
  std::vector<RegisteredGateDecl> gate_decls_;

  uint8_t reject_pulse_pct_ = 100;
  uint8_t error_pulse_pct_ = 100;

  std::unordered_map<std::string, PulseStyle> path_output_pulse_styles_;
  bool has_global_pulse_style_ = false;
  PulseStyle global_pulse_style_ = PulseStyle::kOnEvent;

  TimingCheckInvocationOptions timing_check_options_;

  std::unordered_map<std::string, ShowCancelled> path_output_showcancelled_;
  bool has_global_showcancelled_ = false;
  ShowCancelled global_showcancelled_ = ShowCancelled::kNoshowcancelled;
};

// Registers onto `mgr` what one module's specify blocks declare, so a design's
// own specify blocks reach the run rather than being parsed and dropped.
// `blocks` are that module's ModuleItem entries of kind
// ModuleItemKind::kSpecifyBlock, in declaration order.
//
// Syntax 30-1 (§30.3) lists five kinds of specify_item: specparam_declaration,
// pulsestyle_declaration, showcancelled_declaration, path_declaration and
// system_timing_check. All five are registered here -- the module path delays
// of §30.4, the specparam declarations of §30.3, the PATHPULSE$ pulse limits of
// §30.7.1, the pulsestyle and showcancelled declarations of §30.7.4, and the
// system timing checks of Clause 31.
//
// The timing checks are registered through
// SpecifyManager::AddTimingCheckUnderOptions, which is what gives §32.4.2's SDF
// TIMINGCHECK annotation a declared check to land on. Registering a check does
// not evaluate it: the watchers that report a violation are armed by
// WatchTimingChecks (src/simulator/timing_check_driver.h), which runs once over
// the whole design after every module has been registered.
//
// The specparam declarations are bound through
// SpecifyManager::BindDesignSpecparams, which is what lets §32.4.3's LABEL
// annotation reach them. Only the specparams declared inside a specify block
// are bound, because only the blocks are passed in; §6.20.5's other declaration
// site, the module body outside every specify block, is bound by
// RegisterModuleSpecparams below.
//
// The module path delays are registered before the PATHPULSE$ specparams are
// resolved, and every PATHPULSE$ specparam of every block is resolved in one
// call to SpecifyManager::ResolvePulseControlSpecparams at the end. §30.7.1
// requires both orderings: a PATHPULSE$ specparam naming no module path applies
// to all module paths defined in the module, so the paths have to exist first,
// and a path-specific PATHPULSE$ specparam takes precedence over a
// nonpath-specific one for the paths it names, which is a rule about
// specificity and not about the order the specparams were declared in.
//
// Call this only after the module's specparams have been lowered as variables
// in `ctx`. The delay expressions of §30.5 and the limit expressions of
// Syntax 30-7 are evaluated in `ctx`, and a specparam an expression reads is
// read from there.
//
// `inst_prefix` is the hierarchical prefix of the module instance the blocks
// were declared in, ending in a `.`, and is empty for a module elaborated as a
// top. §30.4 has a module path name its terminals by the declaring module's own
// port names, so two instances of one cell declare paths spelled identically;
// the prefix is recorded on each path as PathDelay::inst_prefix and on each
// PATHPULSE$ specparam as PulseControlSpecparam::inst_prefix, which is what
// tells the two instances apart.
void RegisterSpecifyBlocks(const std::vector<ModuleItem*>& blocks,
                           std::string_view inst_prefix, SimContext& ctx,
                           Arena& arena, SpecifyManager& mgr);

// §32.4.1: register the module-output drivers of `gates`, the §28.4 gate
// instantiations of one module instance, so that a DEVICE entry finding no
// specify path for an output can still land on the primitive driving it.
// `gates` is RtlirModule::gate_insts (src/elaborator/rtlir.h).
//
// This is a sibling of RegisterSpecifyBlocks rather than a sixth parameter of
// it: five is what readability-function-size.ParameterThreshold in
// etc/clang_tidy/src.yml allows.
//
// Call it under the same conditions RegisterSpecifyBlocks is called under. A
// gate's propagation delay may be written as a specparam, so it is evaluated in
// `ctx` the way a module path delay is and the module's specparams must already
// be lowered as variables there. `inst_prefix` is the instance the gates were
// instantiated in, recorded on each driver as PrimitiveDriver::inst_prefix.
void RegisterModuleGates(const std::vector<ModuleItem*>& gates,
                         std::string_view inst_prefix, SimContext& ctx,
                         Arena& arena, SpecifyManager& mgr);

// §6.20.5: bind the specparams one module instance declared in its module body,
// outside every specify block -- "A specparam ... may be declared inside a
// specify block or in the module body" -- to SpecifyManager, so §32.4.3's LABEL
// annotation reaches them as it reaches the ones RegisterSpecifyBlocks binds.
// §32.4.3 states no exception for either declaration site.
// `names` is RtlirModule::specparam_names (src/elaborator/rtlir.h), each entry
// the name the specparam was lowered under.
//
// This is a sibling of RegisterSpecifyBlocks rather than a sixth parameter of
// it, for the reason RegisterModuleGates is: five is what
// readability-function-size.ParameterThreshold in etc/clang_tidy/src.yml
// allows.
//
// The names are bound under `inst_prefix` because §6.20.5 has the declaration
// name the specparam by a bare name, while Lowerer::CreateChildModuleVariables
// keys an instantiated module's specparam under its instance prefix. Only the
// name has to reach `mgr`: the storage the annotated value is written into
// already exists, Elaborator::ElaborateSpecparam
// (src/elaborator/elaborator_items.cpp) having lowered the specparam as a
// variable of the module declaring it. `ctx` and `arena` are where
// SpecifyManager::ApplyAnnotatedSpecparam finds and rewrites that storage.
void RegisterModuleSpecparams(const std::vector<std::string_view>& names,
                              std::string_view inst_prefix, SimContext& ctx,
                              Arena& arena, SpecifyManager& mgr);

}  // namespace delta
