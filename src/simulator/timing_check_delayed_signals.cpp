// §31.9.1 (printed pages 920-922) and §31.9.4 (printed page 923): the timing
// checks produce delayed copies of their data and reference signals, and a
// check may declare those copies by name so that the model's functional code
// can read them. The elaborator declares each named one as a net of the module
// (elaborator_delayed_signals.cpp); what drives it is here.
//
// Without the option enabling negative timing checks the delayed signals are
// plain copies of the originals, so a copy follows at once. With it they lag
// by the delays SpecifyManager::ResolveNegativeTimingCheckDelays
// (simulator/timing_check_negative_delays.cpp) settles across every check. A
// signal given a delayed copy in some checks and not in others uses that
// delayed copy in all of them, so the delay belongs to the original signal,
// whichever check names the copy.
//
// Each transition of the original reaches the copy the same delay later,
// however close the next one follows: a delayed copy carries the signal, not a
// computed value an inertial delay could filter.

#include "simulator/timing_check_delayed_signals.h"

#include <cstddef>
#include <cstdint>
#include <map>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "parser/ast_specify.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"
#include "simulator/timing_check_driver_internal.h"
#include "simulator/variable.h"

namespace delta {
namespace {

// One named delayed signal: the original it copies, with the select its
// terminal was written with, and where the copy lands.
struct DelayedCopy {
  std::string source;
  TerminalSelect select;
  std::string target;
  bool indexed = false;
  int64_t index = 0;
};

// The copies the registered checks name, keyed by the copy so that a copy two
// checks name is driven once.
struct DelayedCopyPlan {
  std::vector<DelayedCopy> copies;
  std::map<std::string, bool> planned;

  void Add(const std::string& prefix, const std::string& signal,
           const TerminalSelect& select, const DelayedSignalTarget& target) {
    if (target.name.empty()) return;
    std::string key = prefix + target.name;
    if (target.indexed) key += "[" + std::to_string(target.index) + "]";
    if (planned[key]) return;
    planned[key] = true;
    copies.push_back({prefix + signal, select, prefix + target.name,
                      target.indexed, target.index});
  }
};

// The copies $setuphold and $recrem declare. How far each lags its original is
// SpecifyManager::TimingCheckSignalDelay's answer, which §31.9.1 makes a
// property of the original signal whichever check names the copy.
DelayedCopyPlan PlanCopies(const SpecifyManager& mgr) {
  DelayedCopyPlan plan;
  for (const TimingCheckEntry& e : mgr.GetTimingChecks()) {
    if (e.kind != TimingCheckKind::kSetuphold &&
        e.kind != TimingCheckKind::kRecrem) {
      continue;
    }
    plan.Add(e.inst_prefix, e.ref_signal, e.ref_select, e.delayed_ref);
    plan.Add(e.inst_prefix, e.data_signal, e.data_select, e.delayed_data);
  }
  return plan;
}

// The bits of the original the copy carries, least significant first.
Logic4Vec CopiedValue(const Variable& src, const std::vector<uint32_t>& bits,
                      Arena& arena) {
  const uint32_t kWidth =
      bits.empty() ? src.value.width : static_cast<uint32_t>(bits.size());
  Logic4Vec out = MakeLogic4Vec(arena, kWidth);
  for (uint32_t i = 0; i < kWidth; ++i) {
    const uint32_t kFrom = bits.empty() ? i : bits[i];
    const uint32_t kWord = kFrom / 64U;
    if (kWord >= src.value.nwords) continue;
    const uint64_t kBit = (src.value.words[kWord].aval >> (kFrom % 64U)) & 1U;
    const uint64_t kUnk = (src.value.words[kWord].bval >> (kFrom % 64U)) & 1U;
    out.words[i / 64U].aval |= kBit << (i % 64U);
    out.words[i / 64U].bval |= kUnk << (i % 64U);
  }
  return out;
}

void SetBit(Logic4Vec& v, uint32_t bit, const Logic4Vec& from, uint32_t src) {
  const uint64_t kMask = 1ULL << (bit % 64U);
  Logic4Word& w = v.words[bit / 64U];
  w.aval &= ~kMask;
  w.bval &= ~kMask;
  if (src >= from.width) return;
  const Logic4Word& f = from.words[src / 64U];
  if (((f.aval >> (src % 64U)) & 1U) != 0U) w.aval |= kMask;
  if (((f.bval >> (src % 64U)) & 1U) != 0U) w.bval |= kMask;
}

// Where a copy lands: a driver slot of its net, or the variable the module
// declared it as.
struct CopyTarget {
  Net* net = nullptr;
  Variable* var = nullptr;
  bool indexed = false;
  int64_t index = 0;
  std::size_t slot = 0;
  bool has_slot = false;
};

// A copy written `name[index]` sets that bit alone; a net's slot stands at z
// in every other bit, so copies of other bits can drive the same net.
// The value the target is given: the copy in the bits it covers and, where it
// was written `name[index]`, the variable's other bits as they stand, or z in
// a net's slot.
Logic4Vec TargetValue(const CopyTarget& t, const Variable& shape,
                      const Logic4Vec& value, Arena& arena) {
  Logic4Vec out = MakeLogic4Vec(arena, shape.value.width);
  if (!t.indexed) {
    for (uint32_t i = 0; i < out.width; ++i) SetBit(out, i, value, i);
    return out;
  }
  for (uint32_t w = 0; w < out.nwords; ++w) {
    out.words[w] =
        t.net != nullptr ? Logic4Word{0, ~0ULL} : shape.value.words[w];
  }
  const PackedRange kRange = shape.DeclaredRange();
  if (kRange.Contains(t.index)) {
    SetBit(out, static_cast<uint32_t>(kRange.OffsetOf(t.index)), value, 0);
  }
  return out;
}

void WriteCopy(CopyTarget& t, const Logic4Vec& value, SimContext& ctx,
               Arena& arena) {
  Variable* shape = t.net != nullptr ? t.net->resolved : t.var;
  if (shape == nullptr) return;
  Logic4Vec out = TargetValue(t, *shape, value, arena);
  if (t.net == nullptr) {
    t.var->value = out;
    t.var->NotifyWatchers();
    return;
  }
  if (!t.has_slot) {
    t.slot = t.net->drivers.size();
    t.net->drivers.push_back(out);
    t.net->driver_strengths.push_back(DriverStrength{});
    t.has_slot = true;
  } else {
    t.net->drivers[t.slot] = out;
  }
  t.net->Resolve(arena, &ctx.GetScheduler());
}

void InstallCopy(const DelayedCopy& copy, uint64_t delay, SimContext& ctx,
                 Arena& arena) {
  Variable* src = ctx.FindVariable(copy.source);
  if (src == nullptr) return;
  auto target = std::make_shared<CopyTarget>();
  target->net = ctx.FindNet(copy.target);
  if (target->net == nullptr) target->var = ctx.FindVariable(copy.target);
  if (target->net == nullptr && target->var == nullptr) return;
  target->indexed = copy.indexed;
  target->index = copy.index;
  std::vector<uint32_t> bits = SelectedBitOffsets(copy.select, *src);
  WriteCopy(*target, CopiedValue(*src, bits, arena), ctx, arena);
  src->AddWatcher([src, bits, target, delay, &ctx, &arena]() {
    Logic4Vec value = CopiedValue(*src, bits, arena);
    if (delay == 0) {
      WriteCopy(*target, value, ctx, arena);
      return false;
    }
    auto* event = ctx.GetScheduler().GetEventPool().Acquire();
    event->callback = [target, value, &ctx, &arena]() {
      WriteCopy(*target, value, ctx, arena);
    };
    ctx.GetScheduler().ScheduleEvent(SimTime{ctx.CurrentTime().ticks + delay},
                                     Region::kActive, event);
    return false;
  });
}

}  // namespace

void DriveTimingCheckDelayedSignals(const SpecifyManager& mgr, SimContext& ctx,
                                    Arena& arena) {
  DelayedCopyPlan plan = PlanCopies(mgr);
  for (const DelayedCopy& copy : plan.copies) {
    InstallCopy(copy, mgr.TimingCheckSignalDelay(copy.source), ctx, arena);
  }
}

}  // namespace delta
