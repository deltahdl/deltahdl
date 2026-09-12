#pragma once

#include <array>
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

  bool IsKnown() const;
  bool IsTruthy() const;

  // Numeric/boolean projection, not a raw-word accessor: x and z bits read as
  // 0 (the SystemVerilog 4-state-to-2-state cast). Code that rebuilds a 4-state
  // value must read words[w].aval / words[w].bval directly. Going through
  // ToUint64 reads x=(1,1) and z=(0,1) alike as 0, and it returns words[0]
  // alone, so a value rebuilt from what it hands back is two-state and no
  // wider than 64 bits.
  uint64_t ToUint64() const;
  std::string ToString() const;

  // Whether `other` is the same value: the same width, and the same 0, 1, x or
  // z in every bit position. This is what a value change is measured against,
  // so it is a bit-for-bit identity rather than a numeric comparison -- two
  // values ToUint64 answers the same for can differ in width and in every
  // unknown bit, since that projection reads one word and collapses x and z
  // alike to 0.
  bool SameValueAs(const Logic4Vec& other) const;
};

// A copy of a Logic4Vec that owns the words it holds.
//
// Copying a Logic4Vec copies its `words` pointer rather than the words, so a
// plain copy kept as a baseline and compared against the original later is the
// original, and the comparison can only ever report no change. That is a
// distinction because a write does not always replace the words it writes:
// DepositBitField writes through them, which is how a packed struct or union
// member assignment lands, and several sites assign into `value.words[i]`
// directly. A baseline meant to survive such a write has to own its words, and
// this is what owns them.
//
// The captured view points into this object's own storage, so the copy and
// move operations are written out: the implicit ones would leave the copy's
// view pointing at the source's words, which is the aliasing this type exists
// to remove.
class Logic4Snapshot {
 public:
  Logic4Snapshot() = default;
  Logic4Snapshot(const Logic4Snapshot& other) { *this = other; }
  Logic4Snapshot& operator=(const Logic4Snapshot& other);
  Logic4Snapshot(Logic4Snapshot&& other) noexcept { *this = std::move(other); }
  Logic4Snapshot& operator=(Logic4Snapshot&& other) noexcept;
  ~Logic4Snapshot() = default;

  // Copies src's words into storage this owns. The storage already held is
  // reused, so recapturing the same variable over and over -- which every
  // event control does, on each notification that does not qualify --
  // allocates at most once.
  void Capture(const Logic4Vec& src);

  // The captured value, as a Logic4Vec over the words this owns.
  const Logic4Vec& Get() const { return view_; }

 private:
  std::vector<Logic4Word> words_;
  Logic4Vec view_{};
};

Logic4Vec MakeLogic4Vec(class Arena& arena, uint32_t width);
Logic4Vec MakeLogic4VecVal(class Arena& arena, uint32_t width, uint64_t val);

// The bits word `word_index` of a `width`-bit vector holds: every bit of a
// word wholly inside the width, and the low `width % 64` of the word the width
// ends in. MakeLogic4Vec rounds the allocation up to whole words, so a
// producer that writes a word at a time has bits above the width to decide
// about, and the answer is always that they stay clear: they are not part of
// the value. ToString and ToUint64 stop at the width and so cannot show them,
// while the word-wise readers -- EvalCaseEquality, which §11.4.5 has compare x
// and z bits for equality, among them -- compare them like any other bit. A
// producer that set them therefore prints the same as one that did not and
// compares differently, which is the disagreement this exists to prevent.
uint64_t WordMaskWithinWidth(uint32_t width, uint32_t word_index);

// Sets every bit inside `vec.width` to x -- Convention A's (aval=1, bval=1) --
// and leaves the bits above it clear. §6.8's Table 6-7 gives an uninitialized
// 4-state integral object this value, and it is produced in four places: the
// two that allocate storage for a variable, the one behind MakeAllX, and the
// one that puts a port's default back over a net's z.
void FillWithX(Logic4Vec& vec);

// Extract `width` bits starting at `start_bit` from `src` into a fresh vector
// of that width, preserving 4-state encoding. Bits at or beyond src.width read
// as 0. Multi-word safe (unlike a ToUint64()-based slice, which loses bits >=
// 64).
Logic4Vec ExtractBitField(class Arena& arena, const Logic4Vec& src,
                          uint32_t start_bit, uint32_t width);

// Deposit the low `width` bits of `src` into `dst` starting at `start_bit`,
// preserving every other bit of `dst` (4-state encoding kept on both sides).
// Multi-word safe: writes the correct word/bit even when start_bit >= 64.
void DepositBitField(Logic4Vec& dst, uint32_t start_bit, const Logic4Vec& src,
                     uint32_t width);

struct Logic2Vec {
  uint32_t width = 0;
  uint32_t nwords = 0;
  uint64_t* words = nullptr;

  uint64_t ToUint64() const;
};

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

// §28.11 partitions the strength scale of Table 28-7 into the four driving
// strengths (supply, strong, pull, weak) and the three charge storage
// strengths (large, medium, small). highz belongs to neither group.
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

// The text a TimeUnit is written as -- "s", "ms", "us", "ns", "ps" or
// "fs" -- which is what ParseTimeUnitStr reads back. §3.14.2.1 gives that
// set as the time_literal unit, and Syntax 21-20's time_unit repeats it, so
// a caller spelling a time unit for either has the same six names to choose
// from.
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

// Annex E: the compiler directives of the annex in force where a module was
// declared, E.2's default decay time, E.3's default charge strength and the
// delay mode of E.4 to E.7. Each directive applies to the modules that follow
// it in the source, so the preprocessor records the values in force at each
// module header under the module's name, and the values reach the declaration
// by that name once the module is parsed. `decay_ticks` is the decay time as
// the directive's argument was rounded and `decay_infinite` the state E.2's
// keyword names, and the state before any directive; `has_strength` is whether
// a strength directive came before the module and `strength` the last one's
// value; `delay_mode` is the last delay mode directive before the module, or
// kNone where none came.
struct ModuleDirectives {
  std::string module;
  uint64_t decay_ticks = 0;
  bool decay_infinite = true;
  uint32_t strength = 0;
  bool has_strength = false;
  DelayModeDirective delay_mode = DelayModeDirective::kNone;
};

// Which member of a min:typ:max expression is selected. §11.11 orders the
// three as the minimum, the typical and the maximum, and has the three there
// so a design can be tested under any one of them, so one of the three is
// chosen for a whole run rather than per expression.
//
// This is not DelayModeDirective above, which carries the `delay_mode_path
// family that Preprocessor::ProcessDelayModeDirective in
// src/preprocessor/preprocessor_lines.cpp accepts and which selects nothing
// among three values. §22.1 lists the compiler directives alphabetically and
// names none of that family; Annex E.4 to E.7 describe them, and that function
// reports each under its own subclause there.
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
