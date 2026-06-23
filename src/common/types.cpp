#include "common/types.h"

#include <cmath>
#include <sstream>

#include "common/arena.h"

namespace delta {

Logic4Word Logic4And(Logic4Word a, Logic4Word b) {
  uint64_t a_known_0 = ~a.aval & ~a.bval;
  uint64_t b_known_0 = ~b.aval & ~b.bval;
  uint64_t result_aval = a.aval & b.aval;
  uint64_t any_known_0 = a_known_0 | b_known_0;
  uint64_t result_bval = (a.bval | b.bval) & ~any_known_0;
  return {result_aval & ~result_bval, result_bval};
}

Logic4Word Logic4Or(Logic4Word a, Logic4Word b) {
  uint64_t a_known_1 = a.aval & ~a.bval;
  uint64_t b_known_1 = b.aval & ~b.bval;
  uint64_t result_aval = a.aval | b.aval;
  uint64_t any_known_1 = a_known_1 | b_known_1;
  uint64_t result_bval = (a.bval | b.bval) & ~any_known_1;
  return {result_aval & ~result_bval, result_bval};
}

Logic4Word Logic4Xor(Logic4Word a, Logic4Word b) {
  uint64_t unknown = a.bval | b.bval;
  uint64_t result_aval = a.aval ^ b.aval;
  return {result_aval & ~unknown, unknown};
}

Logic4Word Logic4Not(Logic4Word a) {
  // Bitwise negation: ~0->1, ~1->0, ~x->x, ~z->x. An unknown input bit
  // (bval=1, i.e. x or z) yields x, whose canonical 4-state encoding is
  // (aval=1, bval=1) -- matching MakeAllX. Forcing aval high on unknown bits
  // (rather than leaving the inverted level) keeps ~z from collapsing to the
  // z encoding (0,1).
  return {(~a.aval & ~a.bval) | a.bval, a.bval};
}

bool Logic4Vec::IsKnown() const {
  for (uint32_t i = 0; i < nwords; ++i) {
    if (words[i].bval != 0) {
      return false;
    }
  }
  return true;
}

bool Logic4Vec::IsTruthy() const {
  for (uint32_t i = 0; i < nwords; ++i) {
    if (words[i].aval & ~words[i].bval) {
      return true;
    }
  }
  return false;
}

uint64_t Logic4Vec::ToUint64() const {
  if (nwords == 0) {
    return 0;
  }
  return words[0].aval;
}

std::string Logic4Vec::ToString() const {
  std::string result;
  result.reserve(width);
  for (int32_t i = static_cast<int32_t>(width) - 1; i >= 0; --i) {
    uint32_t word_idx = static_cast<uint32_t>(i) / 64;
    uint32_t bit_idx = static_cast<uint32_t>(i) % 64;
    uint64_t mask = uint64_t(1) << bit_idx;
    bool a = (words[word_idx].aval & mask) != 0;
    bool b = (words[word_idx].bval & mask) != 0;
    if (!b && !a) {
      result += '0';
    } else if (!b && a) {
      result += '1';
    } else if (b && !a) {
      result += 'x';
    } else {
      result += 'z';
    }
  }
  return result;
}

Logic4Vec MakeLogic4Vec(Arena& arena, uint32_t width) {
  uint32_t nwords = (width + 63) / 64;
  auto* words = arena.AllocArray<Logic4Word>(nwords);
  return {width, nwords, words};
}

Logic4Vec MakeLogic4VecVal(Arena& arena, uint32_t width, uint64_t val) {
  auto vec = MakeLogic4Vec(arena, width);
  if (vec.nwords > 0) {
    if (width < 64) val &= (uint64_t{1} << width) - 1;
    vec.words[0].aval = val;
  }
  return vec;
}

uint64_t Logic2Vec::ToUint64() const {
  if (nwords == 0) {
    return 0;
  }
  return words[0];
}

Strength ReduceNonresistive(Strength input) {
  return input == Strength::kSupply ? Strength::kStrong : input;
}

Strength ReduceResistive(Strength input) {
  switch (input) {
    case Strength::kSupply:
    case Strength::kStrong:
      return Strength::kPull;
    case Strength::kPull:
      return Strength::kWeak;
    case Strength::kLarge:
    case Strength::kWeak:
      return Strength::kMedium;
    case Strength::kMedium:
    case Strength::kSmall:
      return Strength::kSmall;
    case Strength::kHighz:
      return Strength::kHighz;
  }
  return input;
}

bool IsDrivingStrength(Strength input) {
  switch (input) {
    case Strength::kSupply:
    case Strength::kStrong:
    case Strength::kPull:
    case Strength::kWeak:
      return true;
    default:
      return false;
  }
}

bool IsChargeStorageStrength(Strength input) {
  switch (input) {
    case Strength::kLarge:
    case Strength::kMedium:
    case Strength::kSmall:
      return true;
    default:
      return false;
  }
}

bool IsActiveRegionSet(Region r) {
  switch (r) {
    case Region::kActive:
    case Region::kInactive:
    case Region::kPreNBA:
    case Region::kNBA:
    case Region::kPostNBA:
      return true;
    default:
      return false;
  }
}

bool IsReactiveRegionSet(Region r) {
  switch (r) {
    case Region::kReactive:
    case Region::kReInactive:
    case Region::kPreReNBA:
    case Region::kReNBA:
    case Region::kPostReNBA:
      return true;
    default:
      return false;
  }
}

bool IsIterativeRegion(Region r) {
  switch (r) {
    case Region::kActive:
    case Region::kInactive:
    case Region::kPreNBA:
    case Region::kNBA:
    case Region::kPostNBA:
    case Region::kPreObserved:
    case Region::kObserved:
    case Region::kPostObserved:
    case Region::kReactive:
    case Region::kReInactive:
    case Region::kPreReNBA:
    case Region::kReNBA:
    case Region::kPostReNBA:
    case Region::kPrePostponed:
      return true;
    default:
      return false;
  }
}

bool IsSimulationRegion(Region r) {
  switch (r) {
    case Region::kPreponed:
    case Region::kActive:
    case Region::kInactive:
    case Region::kNBA:
    case Region::kObserved:
    case Region::kReactive:
    case Region::kReInactive:
    case Region::kReNBA:
    case Region::kPostponed:
      return true;
    default:
      return false;
  }
}

bool IsPliRegion(Region r) {
  switch (r) {
    case Region::kPreponed:
    case Region::kPreActive:
    case Region::kPreNBA:
    case Region::kPostNBA:
    case Region::kPreObserved:
    case Region::kPostObserved:
    case Region::kPreReNBA:
    case Region::kPostReNBA:
    case Region::kPrePostponed:
      return true;
    default:
      return false;
  }
}

int EffectiveTimeOrder(TimeUnit unit, int magnitude) {
  int order = static_cast<int>(unit);
  if (magnitude == 10)
    order += 1;
  else if (magnitude == 100)
    order += 2;
  return order;
}

bool ParseTimeUnitStr(std::string_view str, TimeUnit& out) {
  if (str == "s") {
    out = TimeUnit::kS;
  } else if (str == "ms") {
    out = TimeUnit::kMs;
  } else if (str == "us") {
    out = TimeUnit::kUs;
  } else if (str == "ns") {
    out = TimeUnit::kNs;
  } else if (str == "ps") {
    out = TimeUnit::kPs;
  } else if (str == "fs") {
    out = TimeUnit::kFs;
  } else {
    return false;
  }
  return true;
}

static uint64_t PowerOf10(int exp) {
  uint64_t result = 1;
  for (int i = 0; i < exp; ++i) result *= 10;
  return result;
}

uint64_t DelayToTicks(uint64_t delay, const TimeScale& scale,
                      TimeUnit global_precision) {
  int exp_diff =
      static_cast<int>(scale.unit) - static_cast<int>(global_precision);
  uint64_t ticks = delay * scale.magnitude;
  if (exp_diff > 0) {
    ticks *= PowerOf10(exp_diff);
  } else if (exp_diff < 0) {
    ticks /= PowerOf10(-exp_diff);
  }
  return ticks;
}

uint64_t RealDelayToTicks(double delay, const TimeScale& scale,
                          TimeUnit global_precision) {
  int exp_diff =
      static_cast<int>(scale.unit) - static_cast<int>(global_precision);
  double raw_ticks = delay * scale.magnitude;
  if (exp_diff > 0) {
    raw_ticks *= static_cast<double>(PowerOf10(exp_diff));
  } else if (exp_diff < 0) {
    raw_ticks /= static_cast<double>(PowerOf10(-exp_diff));
  }

  int prec_diff =
      static_cast<int>(scale.precision) - static_cast<int>(global_precision);
  double prec_step = scale.prec_magnitude;
  if (prec_diff > 0) {
    prec_step *= static_cast<double>(PowerOf10(prec_diff));
  }

  double rounded = std::round(raw_ticks / prec_step) * prec_step;
  return static_cast<uint64_t>(rounded);
}

}  // namespace delta
