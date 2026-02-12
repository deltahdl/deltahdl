#pragma once

#include <array>
#include <cstdint>
#include <string>
#include <vector>

namespace delta {

// --- Four-value logic (IEEE 1800-2023 §6.3) ---
// Dual-rail aval/bval encoding per VPI convention:
//   0: aval=0, bval=0
//   1: aval=1, bval=0
//   x: aval=0, bval=1
//   z: aval=1, bval=1

struct Logic4Word {
  uint64_t aval = 0;
  uint64_t bval = 0;

  bool IsKnown() const { return bval == 0; }
  bool IsZero() const { return aval == 0 && bval == 0; }
  bool IsOne() const { return aval == 1 && bval == 0; }
};

Logic4Word Logic4And(Logic4Word a, Logic4Word b);
Logic4Word Logic4Or(Logic4Word a, Logic4Word b);
Logic4Word Logic4Xor(Logic4Word a, Logic4Word b);
Logic4Word Logic4Not(Logic4Word a);

struct Logic4Vec {
  uint32_t width = 0;
  uint32_t nwords = 0;
  Logic4Word* words = nullptr;
  bool is_real = false;    // True when value holds IEEE 754 double bits.
  bool is_signed = false;  // True when value should be treated as signed.

  bool IsKnown() const;
  uint64_t ToUint64() const;
  std::string ToString() const;
};

Logic4Vec MakeLogic4Vec(class Arena& arena, uint32_t width);
Logic4Vec MakeLogic4VecVal(class Arena& arena, uint32_t width, uint64_t val);

// --- Two-state logic (bit, int, byte, etc.) ---

struct Logic2Vec {
  uint32_t width = 0;
  uint32_t nwords = 0;
  uint64_t* words = nullptr;

  uint64_t ToUint64() const;
};

// --- Signal strength (IEEE 1800-2023 §6.3.2) ---

enum class Strength : uint8_t {
  kHighz = 0,
  kSmall = 1,
  kMedium = 2,
  kWeak = 3,
  kLarge = 4,
  kPull = 5,
  kStrong = 6,
  kSupply = 7,
};

struct StrengthVal {
  uint8_t s0 : 4;
  uint8_t s1 : 4;
  uint8_t val : 2;
};

// --- Simulation time ---

struct SimTime {
  uint64_t ticks = 0;

  bool operator==(const SimTime& o) const { return ticks == o.ticks; }
  bool operator<(const SimTime& o) const { return ticks < o.ticks; }
  bool operator<=(const SimTime& o) const { return ticks <= o.ticks; }
  bool operator>(const SimTime& o) const { return ticks > o.ticks; }

  SimTime operator+(const SimTime& o) const { return {ticks + o.ticks}; }
};

// --- Timescale (IEEE 1800-2023 §22.7) ---

enum class TimeUnit : int8_t {
  kS = 0,
  kMs = -3,
  kUs = -6,
  kNs = -9,
  kPs = -12,
  kFs = -15,
};

struct TimeScale {
  TimeUnit unit = TimeUnit::kNs;
  int magnitude = 1;  // 1, 10, or 100
  TimeUnit precision = TimeUnit::kNs;
  int prec_magnitude = 1;
};

/// Convert a delay value to ticks at a given timescale/precision.
uint64_t DelayToTicks(uint64_t delay, const TimeScale& scale,
                      TimeUnit global_precision);

/// Parse a time unit string (e.g. "ns") to TimeUnit.
/// Returns false if the string is not a valid unit.
bool ParseTimeUnitStr(std::string_view str, TimeUnit& out);

// --- Event scheduler regions (IEEE 1800-2023 §4.4) ---

enum class Region : uint8_t {
  kPreponed,
  kPreActive,
  kActive,
  kInactive,
  kPreNBA,
  kNBA,
  kPostNBA,
  kPreObserved,
  kObserved,
  kPostObserved,
  kReactive,
  kReInactive,
  kPreReNBA,
  kReNBA,
  kPostReNBA,
  kPrePostponed,
  kPostponed,
  kCOUNT
};

static constexpr size_t kRegionCount = static_cast<size_t>(Region::kCOUNT);

// --- Net types (IEEE 1800-2023 §6.5) ---

enum class NetType : uint8_t {
  kWire,
  kTri,
  kWand,
  kTriand,
  kWor,
  kTrior,
  kTri0,
  kTri1,
  kSupply0,
  kSupply1,
  kTrireg,
  kUwire,
  kNone,
  kInterconnect,
};

// --- SmallVec: inline storage for common small sizes ---

template <typename T, size_t N = 4>
class SmallVec {
 public:
  void push_back(const T& val) {
    if (size_ < N) {
      inline_[size_++] = val;
      return;
    }
    if (size_ == N) {
      SpillToHeap();
    }
    heap_.push_back(val);
    ++size_;
  }

  T& operator[](size_t i) { return (size_ <= N) ? inline_[i] : heap_[i]; }

  const T& operator[](size_t i) const {
    return (size_ <= N) ? inline_[i] : heap_[i];
  }

  size_t size() const { return size_; }
  bool empty() const { return size_ == 0; }

  T* data() { return (size_ <= N) ? inline_.data() : heap_.data(); }
  const T* data() const { return (size_ <= N) ? inline_.data() : heap_.data(); }

  T* begin() { return data(); }
  T* end() { return data() + size_; }
  const T* begin() const { return data(); }
  const T* end() const { return data() + size_; }

 private:
  void SpillToHeap() {
    heap_.reserve(N * 2);
    for (size_t i = 0; i < N; ++i) {
      heap_.push_back(inline_[i]);
    }
  }

  size_t size_ = 0;
  std::array<T, N> inline_{};
  std::vector<T> heap_;
};

}  // namespace delta
