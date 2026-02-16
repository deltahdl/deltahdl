#include "common/types.h"

#include <cmath>
#include <sstream>

#include "common/arena.h"

namespace delta {

// --- Logic4Word operations ---

Logic4Word Logic4And(Logic4Word a, Logic4Word b) {
  // Truth table: 0&x=0, 1&x=x, x&x=x
  uint64_t a_known_0 = ~a.aval & ~a.bval;
  uint64_t b_known_0 = ~b.aval & ~b.bval;
  uint64_t result_aval = a.aval & b.aval;
  uint64_t any_known_0 = a_known_0 | b_known_0;
  uint64_t result_bval = (a.bval | b.bval) & ~any_known_0;
  return {result_aval & ~result_bval, result_bval};
}

Logic4Word Logic4Or(Logic4Word a, Logic4Word b) {
  // Truth table: 1|x=1, 0|x=x, x|x=x
  uint64_t a_known_1 = a.aval & ~a.bval;
  uint64_t b_known_1 = b.aval & ~b.bval;
  uint64_t result_aval = a.aval | b.aval;
  uint64_t any_known_1 = a_known_1 | b_known_1;
  uint64_t result_bval = (a.bval | b.bval) & ~any_known_1;
  return {result_aval | result_bval, result_bval};
}

Logic4Word Logic4Xor(Logic4Word a, Logic4Word b) {
  uint64_t unknown = a.bval | b.bval;
  uint64_t result_aval = a.aval ^ b.aval;
  return {result_aval & ~unknown, unknown};
}

Logic4Word Logic4Not(Logic4Word a) { return {~a.aval & ~a.bval, a.bval}; }

// --- Logic4Vec operations ---

bool Logic4Vec::IsKnown() const {
  for (uint32_t i = 0; i < nwords; ++i) {
    if (words[i].bval != 0) {
      return false;
    }
  }
  return true;
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
    // Mask to declared width to prevent stale upper bits.
    if (width < 64) val &= (uint64_t{1} << width) - 1;
    vec.words[0].aval = val;
  }
  return vec;
}

// --- Logic2Vec ---

uint64_t Logic2Vec::ToUint64() const {
  if (nwords == 0) {
    return 0;
  }
  return words[0];
}

// --- Timescale ---

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
  // The delay is in units of (magnitude * unit).
  // Convert to ticks in global_precision.
  // Exponent difference: unit_exp - precision_exp
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
  // Convert delay (in time units) to raw ticks at global precision.
  int exp_diff =
      static_cast<int>(scale.unit) - static_cast<int>(global_precision);
  double raw_ticks = delay * scale.magnitude;
  if (exp_diff > 0) {
    raw_ticks *= static_cast<double>(PowerOf10(exp_diff));
  } else if (exp_diff < 0) {
    raw_ticks /= static_cast<double>(PowerOf10(-exp_diff));
  }

  // Calculate precision step size in ticks at global precision.
  int prec_diff =
      static_cast<int>(scale.precision) - static_cast<int>(global_precision);
  double prec_step = scale.prec_magnitude;
  if (prec_diff > 0) {
    prec_step *= static_cast<double>(PowerOf10(prec_diff));
  }

  // Round to nearest precision step (§3.14.1).
  double rounded = std::round(raw_ticks / prec_step) * prec_step;
  return static_cast<uint64_t>(rounded);
}

}  // namespace delta
