// §28.15.2 and §28.16.2: the charge storage state of a trireg net, bit by bit,
// and the charge decay of each bit that enters it, moved out of
// src/simulator/net.cpp, which resolves a net from its sources, at its size
// limit.

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

// The states Net::charge_since gives a bit besides the tick it entered the
// charge storage state at: a source drives it, or it holds the x the net starts
// with, which no driver left there and which so stands against no source.
constexpr uint64_t kBitDriven = UINT64_MAX;
constexpr uint64_t kBitInitial = UINT64_MAX - 1;

// The value of bit `bit` of `v`: 0, 1, 2 for x and 3 for z.
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

// The strongest level any of `values` drives bit `bit` at, or `strongest`
// where each leaves the bit z. `strengths` holds one entry for each of
// `values`.
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

// The strongest level a source of the net drives bit `bit` at: one of its own
// drivers, or a signal a switch carries to it (§28.8).
Strength StrongestSourceAt(const Net& net,
                           const std::vector<DriverStrength>& own,
                           uint32_t bit) {
  return StrongestAt(net.switch_drivers, net.switch_strengths, bit,
                     StrongestAt(net.drivers, own, bit, Strength::kHighz));
}

// §28.16.2.1: the charge decay time of the bits that entered the charge
// storage state at tick `since` runs out: each of them still holding the
// charge it took then moves from 1 or 0 to x, and the net resolves again with
// that x as its charge, at its charge strength. A bit a source has driven
// since, or one that entered the state again later, is another charge and is
// left alone.
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
  };
  auto time = sched->CurrentTime();
  time.ticks += net.decay_ticks;
  sched->ScheduleEvent(time, Region::kActive, event);
}

}  // namespace

// §28.16.2: a bit enters the charge storage state when every source of it goes
// to high impedance, keeping the value it was driven to, and §28.12 resolves
// each bit of a net on its own, so a bit enters it while others are still
// driven. §28.15.2 has the charge drive at the trireg's charge strength, so it
// stands against a source weaker than that, and the bit leaves the state only
// for a source at least as strong (§28.16.2.1: a driver turning on ends the
// decay when its value gets into the net). The decay of a bit is scheduled
// once, as it enters the state, so neither a source that stays at z nor one the
// charge outranks starts it again or ends it.
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
