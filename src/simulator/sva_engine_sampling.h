#ifndef DELTA_SIMULATOR_SVA_ENGINE_SAMPLING_H_
#define DELTA_SIMULATOR_SVA_ENGINE_SAMPLING_H_

#include <cstddef>
#include <cstdint>
#include <functional>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/types.h"
#include "simulator/sva_engine_sequences.h"

namespace delta {

class Arena;
struct Expr;
struct InstanceBindings;
struct QueueObject;
struct Variable;

enum class AssertionKind : uint8_t {
  kAssert = 0,
  kAssume = 1,
  kCover = 2,
  kRestrict = 3,
};

enum class SequencePropertyStrength : uint8_t {
  kWeak = 0,
  kStrong = 1,
};

SequencePropertyStrength DefaultSequencePropertyStrength(AssertionKind stmt);

PropertyResult EvalStrongSequenceProperty(bool has_nonempty_match);

PropertyResult EvalWeakSequenceProperty(bool finite_prefix_witnesses_inability);

SequencePropertyStrength NegatePropertyStrength(SequencePropertyStrength inner);

bool IsImmediateAssertionKindAllowed(AssertionKind kind);

enum class AssertionTiming : uint8_t {
  kImmediate = 0,
  kConcurrent = 1,
};

bool ConcurrentTimingUsesSampledValues(AssertionTiming timing);

enum class SampleMode : uint8_t {
  kPreponed = 0,
  kCurrent = 1,
  kDefault = 2,
  kPostponed = 3,
};

struct SampledValue {
  uint64_t value = 0;
  SampleMode mode = SampleMode::kPreponed;
};

SampledValue SampleStaticVariable(uint64_t preponed_value, SimTime t,
                                  uint64_t type_default);

SampledValue SampleAutomaticVariable(uint64_t current_value);

SampledValue SampleLocalVariable(uint64_t current_value);

SampledValue SampleActiveFreeCheckerVariable(uint64_t current_value);

SampledValue SampleActiveFreeCheckerVarPastFuture(uint64_t postponed_value);

SampledValue SampleAutomaticVarPastFuture(uint64_t current_value);

SampledValue DefaultSampledValueOfTriggered();
SampledValue DefaultSampledValueOfMatched();

SampledValue SampleSingleVariableExpression(SampledValue var_sample);

SampledValue SampleConstCastExpression(uint64_t argument_current_value);

SampledValue SampleProceduralAssertionArgument(uint64_t current_value);

SampledValue ProceduralArgumentValueAfterMature(
    SampledValue captured, uint64_t later_underlying_value);

enum class ProceduralExecutionEffect : uint8_t {
  kActivation = 0,
  kCompletion = 1,
};

bool ProceduralExecutionAffects(ProceduralExecutionEffect effect,
                                bool already_matured);

SampledValue SampleProceduralAssertionActionBlockArgument(
    uint64_t current_value);

bool ActionBlockMayModifyArgument();

uint64_t ReadProceduralConditionalGuard(uint64_t current_value,
                                        uint64_t sampled_value);

SampledValue SampledValueOfTriggered(bool current_returned);
SampledValue SampledValueOfMatched(bool current_returned);

SampledValue SampleRecursiveExpression(SampledValue a, SampledValue b,
                                       uint64_t (*combinator)(uint64_t,
                                                              uint64_t));

SampledValue DefaultSampledValueOfVariableOrNet(uint64_t type_default);

bool InterpretAssertionExprAsBoolean(uint64_t aval, uint64_t bval);

struct SampledArrayElement {
  uint64_t value = 0;
  bool live = true;
};
SampledArrayElement SampleArrayElementForAssertion(uint64_t element_value);
SampledArrayElement ArrayElementAfterArrayMutation(SampledArrayElement sampled);
bool SampledArrayElementStillReadable(const SampledArrayElement& sampled);

enum class BooleanExprPlace : uint8_t {
  kSequenceOrPropertyExpr = 0,
  kClockingEvent = 1,
  kDisableCondition = 2,
};
bool BooleanExprUsesSampledValues(BooleanExprPlace place);

bool DisableConditionUsesCurrentValues();
bool DisableConditionAllowsTriggeredMethod();
bool DisableConditionAllowsMatchedMethod();
bool DisableConditionAllowsLocalVariableReference();

enum class ClockingInputSkew : uint8_t {
  kStep1 = 0,
  kOther = 1,
};

bool IsClockingBlockInputSamplingValid(ClockingInputSkew skew);

struct SampleSite {
  const Expr* site = nullptr;
  uint64_t variant = 0;
  uint64_t now = 0;
};

class AssertionSampleStore {
 public:
  void Register(const Variable* var, Arena& arena);

  void ExcludeFromSampling(const Variable* var) { excluded_.insert(var); }

  void RegisterQueue(const QueueObject* queue, Arena& arena);

  void Refill(Arena& arena);

  const std::vector<Logic4Vec>* ReadQueueWithinProperty(
      const QueueObject* queue, SimTime t) const;

  const Logic4Vec* Read(const Variable* var, SimTime t) const;

  const Logic4Vec* ReadWithinProperty(const Variable* var, SimTime t) const {
    if (!evaluating_property_ && !procedure_reads_sampled_) return nullptr;
    if (!reading_defaults_) return Read(var, t);
    auto it = entries_.find(var);
    return it == entries_.end() ? nullptr : &it->second.default_value;
  }

  void SetEvaluatingProperty(bool on) { evaluating_property_ = on; }
  bool EvaluatingProperty() const { return evaluating_property_; }

  void SetProcedureReadsSampled(bool on) { procedure_reads_sampled_ = on; }

  void SetInstanceBindings(const InstanceBindings* bindings) {
    bindings_ = bindings;
  }
  const InstanceBindings* Bindings() const { return bindings_; }

  struct OperandRead {
    uint64_t started = 0;
    const Expr* expr = nullptr;
    bool held = false;
  };
  void SetOperandLog(std::vector<OperandRead>* log) { operand_log_ = log; }
  void NoteAttemptStepped(uint64_t started) {
    attempt_started_ = started;
    if (operand_log_ != nullptr)
      operand_log_->push_back({started, nullptr, false});
  }
  void NoteOperand(const Expr* expr, bool held) {
    if (operand_log_ != nullptr) {
      operand_log_->push_back({attempt_started_, expr, held});
    }
  }

  void SetClockTicks(uint32_t ticked) { clock_ticks_ = ticked; }
  uint32_t ClockTicks() const { return clock_ticks_; }

  struct Entry {
    Logic4Vec default_value;
    Logic4Vec preponed_value;
  };
  struct Snapshot {
    SimTime at;
    std::unordered_map<const Variable*, Entry> entries;
  };
  const Snapshot* TakeSnapshot(SimTime t, Arena& arena) const;
  void SetSnapshot(const Snapshot* snapshot) { snapshot_ = snapshot; }
  const Snapshot* InstalledSnapshot() const { return snapshot_; }
  SimTime StepTime(SimTime now) const {
    return snapshot_ != nullptr ? snapshot_->at : now;
  }

  void SetReadingDefaults(bool on) { reading_defaults_ = on; }

  const Logic4Vec* PastValue(const SampleSite& site, uint32_t ticks_back) const;

  void RecordTick(const SampleSite& site, const Logic4Vec& sampled,
                  uint32_t depth, Arena& arena);

  static Logic4Vec OwnedSample(const Logic4Vec& sampled, Arena& arena);

 private:
  struct QueueEntry {
    std::vector<Logic4Vec> default_elements;
    std::vector<Logic4Vec> preponed_elements;
  };

  struct SiteKey {
    const Expr* site;
    uint64_t variant;
    bool operator==(const SiteKey&) const = default;
  };
  struct SiteKeyHash {
    size_t operator()(const SiteKey& key) const {
      return std::hash<const Expr*>()(key.site) ^
             (std::hash<uint64_t>()(key.variant) << 1);
    }
  };

  std::unordered_map<const Variable*, Entry> entries_;
  std::unordered_map<const QueueObject*, QueueEntry> queue_entries_;
  const InstanceBindings* bindings_ = nullptr;
  struct SiteHistory {
    std::vector<Logic4Vec> values;
    uint64_t recorded_at = UINT64_MAX;
  };
  std::unordered_map<SiteKey, SiteHistory, SiteKeyHash> tick_history_;
  std::unordered_set<const Variable*> excluded_;
  bool evaluating_property_ = false;
  bool procedure_reads_sampled_ = false;
  bool reading_defaults_ = false;
  uint32_t clock_ticks_ = ~0u;
  std::vector<OperandRead>* operand_log_ = nullptr;
  uint64_t attempt_started_ = 0;
  const Snapshot* snapshot_ = nullptr;
};

}  // namespace delta

#endif
