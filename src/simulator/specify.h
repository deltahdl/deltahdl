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

class SpecifyManager {
 public:
  void AddPathDelay(PathDelay delay, bool preserve_pulse_limits = false);

  // §32.4.3 (delay expression per §30.5): add a module path from its
  // declaration and hold on to the declaration. Keeping it is what lets the
  // path's delay be recomputed from its own expression later; a path whose
  // delay expression reads a specparam has to follow that specparam when an SDF
  // LABEL changes it, rather than staying at the value the predecessor
  // produced.
  void AddPathDelayFromDecl(const SpecifyPathDecl& decl, SimContext& ctx,
                            Arena& arena);

  void IncrementPathDelay(const PathDelay& delta);

  // §32.4.1: apply one SDF delay entry to the module paths already declared.
  // A nonconditional entry reaches every path between the two ports it names;
  // a conditional or ifnone entry may reach only a path between those same two
  // ports carrying that same condition, and lands nowhere when the module
  // declares no such path rather than inventing one. Returns whether it landed
  // on a declared path. This is the backannotation counterpart of AddPathDelay,
  // which is how a declaration enters the manager in the first place.
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
  bool AnnotateSdfTimingCheck(const SdfTcAnnotation& annotation);

  // §32.4.1: register a module output driven by a gate primitive, so a DEVICE
  // delay that finds no specify path for that output can still land on it.
  void AddPrimitiveDriver(PrimitiveDriver driver);

  // §32.4.3 (drivers per §32.4.1): register every module-output driver one gate
  // instantiation contributes, keeping the gate declaration so its propagation
  // delay expression can be recomputed if an SDF LABEL changes a specparam that
  // expression reads.
  void AddPrimitiveDriversFromGate(const ModuleItem& gate, SimContext& ctx,
                                   Arena& arena);

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
  bool AnnotateSdfDeviceDelay(const SdfDeviceAnnotation& annotation);

  void AnnotateSdf(SdfAnnotation annotation);
  void SetSpecparamValue(SpecparamValue spec);

  void IncrementSpecparamValue(SpecparamValue delta);
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
  // specparams the module declared -- an SDF LABEL annotates to specparams, so
  // a LABEL entry naming anything else must not disturb the design -- and `ctx`
  // is where the design reads their values from. Writing the annotated value
  // there is what makes every later evaluation of an expression containing that
  // specparam, a procedural delay control among them, use the annotated value.
  void BindDesignSpecparams(std::vector<std::string> names, SimContext& ctx,
                            Arena& arena);

  const std::vector<std::string>& GetDeclaredSpecparams() const {
    return declared_specparams_;
  }

  // §32.7: apply one SDF pulse-limit construct to every module path it names.
  // The construct reaches the two limits alone and never the path's delay. Its
  // values either state the limits or, in INCREMENT mode, state amounts to
  // change them by, where an amount that would carry a limit below zero leaves
  // it at zero. Either way a limit the construct puts above the path's delay
  // behaves as one put at the delay.
  void AddSdfPulseLimit(const SdfPulseLimitSpec& spec);

  // §30.7.1: apply the specify block's PATHPULSE$ pulse-control specparams to
  // the module's path delays. A non-path-specific specparam sets the limits of
  // every path; a path-specific specparam overrides only the path it names and
  // takes precedence over any non-path-specific one, regardless of the order in
  // which the specparams were declared.
  void ApplyPathSpecificPulseControl(const PulseControlSpecparam& s);
  void ResolvePulseControlSpecparams(
      const std::vector<PulseControlSpecparam>& specs);

  // §32.7: add the two amounts to the pulse limits of every module path
  // between `src` and `dst`. An annotation that lowers a limit writes its
  // amount as a negative number, so both are signed, and a limit the addition
  // would carry below zero is left at zero instead. An amount of zero names a
  // limit the annotation is not changing at all.
  void IncrementSdfPulseLimit(std::string_view src, std::string_view dst,
                              int64_t reject_delta, int64_t error_delta);

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
  // declaration; absent both, the default is on-event.
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
  // declaration; absent both, the default is noshowcancelled.
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
  void AddTimingCheckUnderOptions(const TimingCheckDecl& decl, SimContext& ctx,
                                  Arena& arena);

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
  void ApplyAnnotatedSpecparam(const std::string& name, uint64_t value);
  // §32.4.3: recompute the expressions that read a changed specparam -- module
  // path delays, timing-check limits, and gate propagation delays -- from their
  // declarations.
  void RebuildPathDelaysForSpecparam(const std::vector<std::string>& changed);
  void RebuildTimingChecksForSpecparam(const std::vector<std::string>& changed);
  void RebuildGateDriversForSpecparam(const std::vector<std::string>& changed);
  void ReplacePrimitiveDriver(PrimitiveDriver rebuilt);

  bool IsDeclaredSpecparam(std::string_view name) const;

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

  // §32.4.3: the design side of a LABEL annotation -- the specparams the module
  // declared, the context and arena its values live in, and the module path
  // declarations kept so their delay expressions can be reevaluated.
  std::vector<std::string> declared_specparams_;
  SimContext* specparam_ctx_ = nullptr;
  Arena* specparam_arena_ = nullptr;
  std::vector<const SpecifyPathDecl*> path_decls_;
  std::vector<const TimingCheckDecl*> timing_check_decls_;
  std::vector<const ModuleItem*> gate_decls_;

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

}  // namespace delta
