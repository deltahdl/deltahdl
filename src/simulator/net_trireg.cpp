#include "simulator/net_trireg.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <vector>

#include "common/types.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

namespace delta {

namespace {

constexpr uint64_t kBitDriven = UINT64_MAX;
constexpr uint64_t kBitInitial = UINT64_MAX - 1;

uint8_t BitOf(const Logic4Vec& v, uint32_t bit) {
  uint64_t mask = uint64_t{1} << (bit % 64);
  const Logic4Word& word = v.words[bit / 64];
  bool aval = (word.aval & mask) != 0;
  if ((word.bval & mask) == 0) return aval ? 1 : 0;
  return aval ? 2 : 3;
}

void CopyBit(Logic4Vec& dst, const Logic4Vec& src, uint32_t bit) {
  uint64_t mask = uint64_t{1} << (bit % 64);
  Logic4Word& to = dst.words[bit / 64];
  const Logic4Word& from = src.words[bit / 64];
  to.aval = (to.aval & ~mask) | (from.aval & mask);
  to.bval = (to.bval & ~mask) | (from.bval & mask);
}

Strength StrongestAt(const std::vector<Logic4Vec>& values,
                     const std::vector<DriverStrength>& strengths, uint32_t bit,
                     Strength strongest) {
  for (size_t i = 0; i < values.size(); ++i) {
    uint8_t v = BitOf(values[i], bit);
    if (v == 3) continue;
    const DriverStrength& ds = strengths[i];
    Strength level = std::max(ds.s0, ds.s1);
    if (v == 0) level = ds.s0;
    if (v == 1) level = ds.s1;
    strongest = std::max(strongest, level);
  }
  return strongest;
}

Strength StrongestSourceAt(const Net& net,
                           const std::vector<DriverStrength>& own,
                           uint32_t bit) {
  return StrongestAt(net.switch_drivers, net.switch_strengths, bit,
                     StrongestAt(net.drivers, own, bit, Strength::kHighz));
}

void ScheduleChargeDecay(Net& net, uint64_t since, Arena& arena,
                         Scheduler* sched) {
  auto* event = sched->GetEventPool().Acquire();
  event->kind = EventKind::kUpdate;
  event->callback = [&net, since, &arena, sched]() {
    Logic4Vec& value = net.resolved->value;
    for (uint32_t b = 0; b < net.charge_since.size(); ++b) {
      if (net.charge_since[b] != since || BitOf(value, b) >= 2) continue;
      uint64_t mask = uint64_t{1} << (b % 64);
      value.words[b / 64].aval |= mask;
      value.words[b / 64].bval |= mask;
    }
    net.Resolve(arena, sched);
    net.resolved->NotifyWatchers();
  };
  auto time = sched->CurrentTime();
  time.ticks += net.decay_ticks;
  sched->ScheduleEvent(time, Region::kActive, event);
}

}  // namespace

std::optional<Logic4Vec> SettleTriregCharge(Net& net, Arena& arena,
                                            Scheduler* sched) {
  uint32_t width = net.resolved->value.width;
  if (net.charge_since.size() != width) {
    net.charge_since.assign(width, kBitInitial);
  }
  std::vector<DriverStrength> own = net.driver_strengths;
  own.resize(net.drivers.size());
  uint64_t now = sched != nullptr ? sched->CurrentTime().ticks : 0;
  Logic4Vec charge = MakeAllHighZ(arena, width);
  bool holds = false;
  bool entered = false;
  for (uint32_t b = 0; b < width; ++b) {
    Strength strongest = StrongestSourceAt(net, own, b);
    uint64_t& since = net.charge_since[b];
    bool charge_stands = since != kBitDriven && since != kBitInitial &&
                         strongest < net.charge_strength;
    if (strongest != Strength::kHighz && !charge_stands) {
      since = kBitDriven;
      continue;
    }
    if (since == kBitDriven) {
      since = now;
      entered = true;
    }
    CopyBit(charge, net.resolved->value, b);
    holds = true;
  }
  if (entered && net.decays && sched != nullptr) {
    ScheduleChargeDecay(net, now, arena, sched);
  }
  if (!holds) return std::nullopt;
  return charge;
}

Logic4Vec TriregStoredCharge(const Net& net, Arena& arena) {
  uint32_t width = net.resolved->value.width;
  Logic4Vec charge = MakeAllHighZ(arena, width);
  for (uint32_t b = 0; b < width; ++b) {
    if (b < net.charge_since.size() && net.charge_since[b] == kBitDriven) {
      continue;
    }
    CopyBit(charge, net.resolved->value, b);
  }
  return charge;
}

}  // namespace delta
