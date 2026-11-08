#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_sdf.h"
#include "simulator/specify_timing_check.h"

namespace delta {

class DiagEngine;
class SimContext;

struct RegisteredPathDecl {
  const SpecifyPathDecl* decl = nullptr;
  std::string inst_prefix;
  std::size_t path_index = 0;
  std::size_t src_index = 0;
  std::size_t dst_index = 0;
};

struct RegisteredTimingCheckDecl {
  const TimingCheckDecl* decl = nullptr;
  std::string inst_prefix;
};

struct RegisteredGateDecl {
  const ModuleItem* gate = nullptr;
  std::string inst_prefix;
};

struct DeclaredSpecparam {
  std::string inst_prefix;
  std::string name;
  const Expr* init = nullptr;
};

class SpecifyManager {
 public:
  void AddPathDelay(PathDelay delay, bool preserve_pulse_limits = false);

  void AddPathDelayFromDecl(const SpecifyPathDecl& decl, SimContext& ctx,
                            Arena& arena, bool default_pulse_limits = false,
                            std::string_view inst_prefix = {});

  bool AnnotateSdfPathDelay(const PathDelay& delay,
                            PathDelayRetention retain = {});

  bool IncrementSdfPathDelay(const PathDelay& target,
                             const SdfPathDelayIncrement& deltas);

  void AddTimingCheck(TimingCheckEntry check);

  bool AnnotateSdfTimingCheck(const SdfTcAnnotation& annotation,
                              std::string_view inst_prefix,
                              std::vector<std::string>& warnings);

  void AddPrimitiveDriver(PrimitiveDriver driver);

  void AddPrimitiveDriversFromGate(
      const ModuleItem& gate, SimContext& ctx, Arena& arena,
      std::string_view inst_prefix = {},
      const std::vector<std::string_view>* module_outputs = nullptr);

  const PrimitiveDriver* FindAnnotatedPrimitiveDriver(
      std::string_view inst_prefix, std::string_view output) const;

  void AnnotateDriverDelays(std::string_view inst_prefix,
                            std::string_view output,
                            const uint64_t (&delays)[3]);

  const std::vector<PrimitiveDriver>& GetPrimitiveDrivers() const {
    return primitive_drivers_;
  }

  bool AnnotateSdfDeviceDelay(const SdfDeviceAnnotation& annotation,
                              std::string_view inst_prefix);

  void SetSpecparamValue(SpecparamValue spec,
                         std::string_view inst_prefix = {});

  void IncrementSpecparamValue(SpecparamValue delta,
                               std::string_view inst_prefix = {});

  bool KnowsSpecparam(std::string_view inst_prefix,
                      std::string_view name) const;
  void AddInterconnectDelay(InterconnectDelay delay);

  void IncrementInterconnectDelay(const InterconnectDelay& delta);

  void BindDesignInterconnect(InterconnectTopology topology);

  const InterconnectTopology& GetInterconnectTopology() const {
    return topology_;
  }

  SdfInterconnectOutcome AnnotateSdfInterconnect(
      const SdfInterconnectAnnotation& annotation);

 private:
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
      const InterconnectTerminal* source) const;
  std::vector<std::string> CoveredSourcesOffNet(
      const InterconnectTerminal* source, const std::string& source_name,
      const std::string& load_name, SdfInterconnectOutcome& out) const;
  void ExtendLoadsUpHierarchy(
      const InterconnectTerminal* source,
      std::vector<const InterconnectTerminal*>& loads) const;
  std::string InterconnectNetIdOf(std::string_view name) const;
  bool DelayLoadCoversReference(const InterconnectDelay& delay,
                                const std::string& net_id,
                                std::string_view name) const;
  std::string AskedSourceNet(std::string_view source) const;
  enum class SourceMatch : uint8_t { kNone, kSameNet, kNamed };
  SourceMatch CoveredSourceMatch(const InterconnectDelay& delay,
                                 std::string_view source,
                                 const std::string& source_net) const;

 public:
  bool HasSourceSpecificInterconnectDelay(std::string_view load) const;

  std::optional<InterconnectDelay> ConnectionInterconnectDelay(
      std::string_view source, std::string_view load) const;

  const InterconnectDelay* FindInterconnectDelay(std::string_view source,
                                                 std::string_view load) const;

  InterconnectReferenceRead ReadInterconnectReference(
      std::string_view name) const;

  void RegisterSpecparamReevaluation(std::string name,
                                     std::function<void(uint64_t)> reevaluate);

  void BindDesignSpecparams(std::vector<std::string> names, SimContext& ctx,
                            Arena& arena, std::string_view inst_prefix = {});

  void RecordSpecparamInitializer(std::string_view inst_prefix,
                                  std::string_view name, const Expr* init);

  const std::vector<DeclaredSpecparam>& GetDeclaredSpecparamsWithInstance()
      const {
    return declared_specparams_;
  }

  std::vector<std::string> GetDeclaredSpecparams() const {
    std::vector<std::string> names;
    names.reserve(declared_specparams_.size());
    for (const auto& declared : declared_specparams_) {
      names.push_back(declared.name);
    }
    return names;
  }

  bool AddSdfPulseLimit(const SdfPulseLimitSpec& spec,
                        std::string_view inst_prefix);

  void ApplyPathSpecificPulseControl(const PulseControlSpecparam& s);
  void ResolvePulseControlSpecparams(
      const std::vector<PulseControlSpecparam>& specs);

  void IncrementSdfPulseLimit(std::string_view src, std::string_view dst,
                              const SdfPulseLimitIncrement& deltas,
                              std::string_view inst_prefix);

  void SetGlobalPulseLimitPercents(uint8_t reject_pct, uint8_t error_pct);

  uint8_t RejectPulseLimitPercent() const { return reject_pulse_pct_; }
  uint8_t ErrorPulseLimitPercent() const { return error_pulse_pct_; }

  void SetPathOutputPulseStyle(std::string output, PulseStyle style);

  void SetGlobalPulseStyle(PulseStyle style);

  PulseStyle ResolvePulseStyle(std::string_view output) const;

  void SetPathOutputShowCancelled(std::string output, ShowCancelled mode);

  void SetGlobalShowCancelled(ShowCancelled mode);

  ShowCancelled ResolveShowCancelled(std::string_view output) const;

  void SetTimingCheckInvocationOptions(TimingCheckInvocationOptions options);

  void ApplyTimingCheckInvocationOptions();

  const TimingCheckInvocationOptions& GetTimingCheckInvocationOptions() const {
    return timing_check_options_;
  }

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
  std::vector<PathDelay>& MutablePathDelays() { return path_delays_; }
  std::vector<TimingCheckEntry>& MutableTimingChecks() {
    return timing_checks_;
  }

  void ResolveNegativeTimingCheckDelays(int64_t unit_ticks, DiagEngine& diag);

  uint64_t TimingCheckSignalDelay(std::string_view signal) const;

  int64_t DelayedSignalShift(const TimingCheckEntry& check) const;

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
  void ApplyAnnotatedSpecparam(std::string_view inst_prefix,
                               const std::string& name, uint64_t value,
                               double real_value);
  std::vector<std::string> ReevaluateDependentSpecparams(
      std::string_view inst_prefix, const std::string& annotated);
  void RebuildPathDelaysForSpecparam(std::string_view inst_prefix,
                                     const std::vector<std::string>& changed);
  void RebuildTimingChecksForSpecparam(std::string_view inst_prefix,
                                       const std::vector<std::string>& changed);
  void RebuildGateDriversForSpecparam(std::string_view inst_prefix,
                                      const std::vector<std::string>& changed);
  void ReplacePrimitiveDriver(PrimitiveDriver rebuilt);

  bool IsDeclaredSpecparam(std::string_view inst_prefix,
                           std::string_view name) const;

  uint64_t StoredSpecparamValue(std::string_view inst_prefix,
                                const std::string& name) const;
  double StoredSpecparamReal(std::string_view inst_prefix,
                             const std::string& name) const;

  const InterconnectDelay* PriorInterconnectDelay(
      const std::string& source, const std::string& load) const;
  void PlaceInterconnectDelay(const SdfInterconnectAnnotation& annotation,
                              const std::string& source,
                              const std::string& load,
                              std::vector<std::string> covered_sources);

  std::vector<PathDelay> path_delays_;
  std::vector<PrimitiveDriver> primitive_drivers_;
  std::vector<TimingCheckEntry> timing_checks_;
  std::unordered_map<std::string, uint64_t> timing_check_signal_delays_;

  std::vector<SpecparamValue> specparam_values_;
  std::unordered_map<std::string, size_t> specparam_index_;
  std::vector<InterconnectDelay> interconnect_delays_;

  InterconnectTopology topology_;

  std::vector<std::pair<std::string, std::function<void(uint64_t)>>>
      specparam_reevaluators_;

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

void RegisterSpecifyBlocks(const std::vector<ModuleItem*>& blocks,
                           std::string_view inst_prefix, SimContext& ctx,
                           Arena& arena, SpecifyManager& mgr);

struct ModuleGates {
  const std::vector<ModuleItem*>& gates;
  const std::vector<std::string_view>& outputs;
};
void RegisterModuleGates(const ModuleGates& module,
                         std::string_view inst_prefix, SimContext& ctx,
                         Arena& arena, SpecifyManager& mgr);

void RegisterModuleSpecparams(const std::vector<std::string_view>& names,
                              std::string_view inst_prefix, SimContext& ctx,
                              Arena& arena, SpecifyManager& mgr);

}  // namespace delta
