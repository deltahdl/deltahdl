#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace delta {

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
  bool is_real = false;
  bool is_signed = false;
  bool is_string = false;
  bool fills_width = false;

  bool IsKnown() const;
  bool IsTruthy() const;

  uint64_t ToUint64() const;
  std::string ToString() const;

  bool SameValueAs(const Logic4Vec& other) const;
};

class Logic4Snapshot {
 public:
  Logic4Snapshot() = default;
  Logic4Snapshot(const Logic4Snapshot& other) { *this = other; }
  Logic4Snapshot& operator=(const Logic4Snapshot& other);
  Logic4Snapshot(Logic4Snapshot&& other) noexcept { *this = std::move(other); }
  Logic4Snapshot& operator=(Logic4Snapshot&& other) noexcept;
  ~Logic4Snapshot() = default;

  void Capture(const Logic4Vec& src);

  const Logic4Vec& Get() const { return view_; }

 private:
  std::vector<Logic4Word> words_;
  Logic4Vec view_{};
};

Logic4Vec MakeLogic4Vec(class Arena& arena, uint32_t width);
Logic4Vec MakeLogic4VecVal(class Arena& arena, uint32_t width, uint64_t val);

uint64_t WordMaskWithinWidth(uint32_t width, uint32_t word_index);

void FillWithX(Logic4Vec& vec);

Logic4Vec ExtractBitField(class Arena& arena, const Logic4Vec& src,
                          uint32_t start_bit, uint32_t width);

void DepositBitField(Logic4Vec& dst, uint32_t start_bit, const Logic4Vec& src,
                     uint32_t width);

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

Strength ReduceNonresistive(Strength input);

Strength ReduceResistive(Strength input);

bool IsDrivingStrength(Strength input);

bool IsChargeStorageStrength(Strength input);

struct SimTime {
  uint64_t ticks = 0;

  bool operator==(const SimTime& o) const { return ticks == o.ticks; }
  bool operator<(const SimTime& o) const { return ticks < o.ticks; }
  bool operator<=(const SimTime& o) const { return ticks <= o.ticks; }
  bool operator>(const SimTime& o) const { return ticks > o.ticks; }

  SimTime operator+(const SimTime& o) const { return {ticks + o.ticks}; }
};

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
  int magnitude = 1;
  TimeUnit precision = TimeUnit::kNs;
  int prec_magnitude = 1;
};

uint64_t DelayToTicks(uint64_t delay, const TimeScale& scale,
                      TimeUnit global_precision);

uint64_t RealDelayToTicks(double delay, const TimeScale& scale,
                          TimeUnit global_precision);

bool ParseTimeUnitStr(std::string_view str, TimeUnit& out);

std::string LiteralTextWithoutSeparators(std::string_view text);

double TimeLiteralValue(std::string_view text, const TimeScale& scale);

std::string_view TimeUnitStr(TimeUnit unit);

int EffectiveTimeOrder(TimeUnit unit, int magnitude);

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

bool IsActiveRegionSet(Region r);

bool IsReactiveRegionSet(Region r);

bool IsIterativeRegion(Region r);

bool IsSimulationRegion(Region r);

bool IsPliRegion(Region r);

enum class DelayModeDirective : uint8_t {
  kNone,
  kDistributed,
  kPath,
  kUnit,
  kZero,
};

enum class DelayMode : uint8_t { kMin, kTyp, kMax };

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

struct ModuleDirectives {
  std::string module;
  uint64_t decay_ticks = 0;
  bool decay_infinite = true;
  uint32_t strength = 0;
  bool has_strength = false;
  DelayModeDirective delay_mode = DelayModeDirective::kNone;
  bool has_timescale = false;
  TimeScale timescale;
  bool is_package = false;
  NetType default_nettype = NetType::kWire;
  NetType unconnected_drive = NetType::kWire;
  bool decay_is_real = false;
  double decay_real = 0.0;
};

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
