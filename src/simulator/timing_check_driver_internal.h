#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_specify.h"
#include "simulator/evaluation.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"

namespace delta {

enum class EdgeLevel : uint8_t {
  kAbsent,
  kZero,
  kOne,
  kUnknown,
};

inline EdgeLevel LevelOfBit(const Logic4Vec& v, uint32_t bit) {
  uint32_t word = bit / 64U;
  if (word >= v.nwords) return EdgeLevel::kAbsent;
  uint64_t mask = 1ULL << (bit % 64U);
  if ((v.words[word].bval & mask) != 0U) return EdgeLevel::kUnknown;
  return (v.words[word].aval & mask) != 0U ? EdgeLevel::kOne : EdgeLevel::kZero;
}

inline std::vector<EdgeLevel> LevelsOfBits(const Logic4Vec& v) {
  std::vector<EdgeLevel> levels;
  levels.reserve(v.width);
  for (uint32_t bit = 0; bit < v.width; ++bit) {
    levels.push_back(LevelOfBit(v, bit));
  }
  return levels;
}

inline EdgeLevel LevelOfDescriptorChar(char c) {
  if (c == '0') return EdgeLevel::kZero;
  if (c == '1') return EdgeLevel::kOne;
  return EdgeLevel::kUnknown;
}

struct TimingCheckEdge {
  SpecifyEdge edge = SpecifyEdge::kNone;
  std::vector<std::pair<char, char>> descriptors;
  TerminalSelect select;
};

inline TimingCheckEdge RefEdgeOf(const TimingCheckEntry& check) {
  return TimingCheckEdge{check.ref_edge, check.ref_edge_descriptors,
                         check.ref_select};
}

inline TimingCheckEdge DataEdgeOf(const TimingCheckEntry& check) {
  return TimingCheckEdge{check.data_edge, check.data_edge_descriptors,
                         check.data_select};
}

inline bool TimingCheckEdgeMatches(const TimingCheckEdge& edge, EdgeLevel from,
                                   EdgeLevel to) {
  if (from == EdgeLevel::kAbsent || to == EdgeLevel::kAbsent) return false;
  if (from == to) return false;
  if (!edge.descriptors.empty()) {
    for (const std::pair<char, char>& descriptor : edge.descriptors) {
      if (LevelOfDescriptorChar(descriptor.first) == from &&
          LevelOfDescriptorChar(descriptor.second) == to) {
        return true;
      }
    }
    return false;
  }
  if (edge.edge == SpecifyEdge::kPosedge) {
    return from == EdgeLevel::kZero || to == EdgeLevel::kOne;
  }
  if (edge.edge == SpecifyEdge::kNegedge) {
    return from == EdgeLevel::kOne || to == EdgeLevel::kZero;
  }
  return true;
}

inline bool TimingCheckSignalTransitioned(const TimingCheckEdge& edge,
                                          const std::vector<EdgeLevel>& before,
                                          const std::vector<EdgeLevel>& after,
                                          const std::vector<uint32_t>& bits) {
  std::size_t width =
      before.size() < after.size() ? before.size() : after.size();
  if (bits.empty()) {
    for (std::size_t bit = 0; bit < width; ++bit) {
      if (TimingCheckEdgeMatches(edge, before[bit], after[bit])) return true;
    }
    return false;
  }
  for (uint32_t bit : bits) {
    if (bit < width && TimingCheckEdgeMatches(edge, before[bit], after[bit])) {
      return true;
    }
  }
  return false;
}

inline std::vector<uint32_t> SelectedBitOffsets(const TerminalSelect& select,
                                                const Variable& var) {
  std::vector<uint32_t> offsets;
  if (!select.present) return offsets;
  const PackedRange kRange = var.DeclaredRange();
  const int64_t kLow = select.left < select.right ? select.left : select.right;
  const int64_t kHigh = select.left < select.right ? select.right : select.left;
  for (int64_t idx = kLow; idx <= kHigh; ++idx) {
    if (kRange.Contains(idx)) {
      offsets.push_back(static_cast<uint32_t>(kRange.OffsetOf(idx)));
    }
  }
  return offsets;
}

inline void WatchEdge(Variable* var, TimingCheckEdge edge,
                      std::function<void()> on_edge) {
  auto seen =
      std::make_shared<std::vector<EdgeLevel>>(LevelsOfBits(var->value));
  std::vector<uint32_t> bits = SelectedBitOffsets(edge.select, *var);
  var->AddWatcher([var, edge = std::move(edge), bits = std::move(bits), seen,
                   on_edge = std::move(on_edge)]() {
    std::vector<EdgeLevel> before = std::move(*seen);
    *seen = LevelsOfBits(var->value);
    if (TimingCheckSignalTransitioned(edge, before, *seen, bits)) on_edge();
    return false;
  });
}

struct ArmedCheck {
  const SpecifyManager* mgr = nullptr;
  std::size_t index = 0;

  const TimingCheckEntry& Entry() const {
    return mgr->GetTimingChecks()[index];
  }
};

inline bool TimingCheckEventEnabled(const Expr* condition,
                                    std::string_view inst_prefix,
                                    SimContext& ctx) {
  if (condition == nullptr) return true;
  InstancePrefixOverride scope(ctx.InstancePrefixOverride(), inst_prefix);
  const Expr* signal = TimingCheckConditioningSignal(condition);
  Logic4Vec value = EvalExpr(signal, ctx, ctx.GetArena());
  if (value.nwords == 0) return false;
  TimingCheckConditionClass form = ClassifyTimingCheckCondition(condition);
  return TimingCheckConditionEnables(form.kind, value.words[0],
                                     form.scalar_constant_bit);
}

struct ConditionedEvent {
  ArmedCheck armed;
  bool is_data_event = false;

  const Expr* Condition() const {
    const TimingCheckEntry& check = armed.Entry();
    return is_data_event ? check.data_condition_expr : check.ref_condition_expr;
  }
};

struct ConditionedEdgeActions {
  std::function<void()> on_edge;
  std::function<void()> on_suppressed;
};

inline void RunConditionedActions(const ConditionedEvent& event,
                                  SimContext& ctx,
                                  const ConditionedEdgeActions& actions) {
  if (TimingCheckEventEnabled(event.Condition(),
                              event.armed.Entry().inst_prefix, ctx)) {
    actions.on_edge();
    return;
  }
  if (actions.on_suppressed) actions.on_suppressed();
}

inline uint64_t DelayedEventLag(const ConditionedEvent& event) {
  const TimingCheckEntry& check = event.armed.Entry();
  if (!EvaluatedOnDelayedSignals(check)) return 0;
  return event.armed.mgr->TimingCheckSignalDelay(
      check.inst_prefix +
      (event.is_data_event ? check.data_signal : check.ref_signal));
}

inline void WatchConditionedEdge(Variable* var, TimingCheckEdge edge,
                                 ConditionedEvent event, SimContext& ctx,
                                 ConditionedEdgeActions actions) {
  WatchEdge(
      var, std::move(edge), [event, &ctx, actions = std::move(actions)]() {
        const uint64_t kLag = DelayedEventLag(event);
        if (kLag == 0) {
          RunConditionedActions(event, ctx, actions);
          return;
        }
        auto* late = ctx.GetScheduler().GetEventPool().Acquire();
        late->callback = [event, &ctx, actions]() {
          RunConditionedActions(event, ctx, actions);
        };
        ctx.GetScheduler().ScheduleEvent(
            SimTime{ctx.CurrentTime().ticks + kLag}, Region::kActive, late);
      });
}

struct ArmedTimingCheckEvents {
  std::string ref_signal;
  std::string data_signal;
};

inline ArmedTimingCheckEvents ArmTimingCheckEvents(
    ArmedCheck armed, SimContext& ctx, const std::function<void()>& on_ref,
    const std::function<void()>& on_data,
    const std::function<void()>& on_ref_suppressed = nullptr) {
  const TimingCheckEntry& check = armed.Entry();
  std::string ref_signal = check.inst_prefix + check.ref_signal;
  std::string data_signal = check.inst_prefix + check.data_signal;
  Variable* ref_var = ctx.FindVariable(ref_signal);
  Variable* data_var = ctx.FindVariable(data_signal);
  if (ref_var == nullptr || data_var == nullptr) return {};
  WatchConditionedEdge(ref_var, RefEdgeOf(check),
                       ConditionedEvent{armed, false}, ctx,
                       {on_ref, on_ref_suppressed});
  WatchConditionedEdge(data_var, DataEdgeOf(check),
                       ConditionedEvent{armed, true}, ctx, {on_data, nullptr});
  return ArmedTimingCheckEvents{std::move(ref_signal), std::move(data_signal)};
}

inline void ScheduleTimingCheckEvaluation(const std::shared_ptr<bool>& pending,
                                          SimContext& ctx,
                                          std::function<void()> evaluate) {
  if (*pending) return;
  *pending = true;
  Event* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = [pending, evaluate = std::move(evaluate)]() {
    *pending = false;
    evaluate();
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kPrePostponed,
                                   event);
}

inline void ReportTimingViolation(std::string_view message,
                                  std::string_view subclause, SourceLoc loc,
                                  SimContext& ctx) {
  ctx.GetDiag().Warning(loc, std::string(message),
                        Subclause(std::string(subclause)));
}

inline void ToggleNotifier(const TimingCheckEntry& check, SimContext& ctx) {
  if (check.notifier.empty()) return;
  Variable* var = ctx.FindVariable(check.inst_prefix + check.notifier);
  if (var == nullptr || var->value.nwords == 0) return;
  Logic4Word toggled = ToggleNotifierOnViolation(var->value.words[0]);
  var->value.words[0].aval =
      (var->value.words[0].aval & ~1ULL) | (toggled.aval & 1ULL);
  var->value.words[0].bval =
      (var->value.words[0].bval & ~1ULL) | (toggled.bval & 1ULL);
  var->NotifyWatchers();
}

inline void NoteViolation(const TimingCheckEntry& check, SimContext& ctx) {
  GetGlobalVpiContext().NoteTimingViolation(check);
  ToggleNotifier(check, ctx);
}

}  // namespace delta
