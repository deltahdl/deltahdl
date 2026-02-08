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

    bool is_known() const { return bval == 0; }
    bool is_zero() const { return aval == 0 && bval == 0; }
    bool is_one() const { return aval == 1 && bval == 0; }
};

Logic4Word logic4_and(Logic4Word a, Logic4Word b);
Logic4Word logic4_or(Logic4Word a, Logic4Word b);
Logic4Word logic4_xor(Logic4Word a, Logic4Word b);
Logic4Word logic4_not(Logic4Word a);

struct Logic4Vec {
    uint32_t width = 0;
    uint32_t nwords = 0;
    Logic4Word* words = nullptr;

    bool is_known() const;
    uint64_t to_uint64() const;
    std::string to_string() const;
};

Logic4Vec make_logic4_vec(class Arena& arena, uint32_t width);
Logic4Vec make_logic4_vec_val(class Arena& arena, uint32_t width, uint64_t val);

// --- Two-state logic (bit, int, byte, etc.) ---

struct Logic2Vec {
    uint32_t width = 0;
    uint32_t nwords = 0;
    uint64_t* words = nullptr;

    uint64_t to_uint64() const;
};

// --- Signal strength (IEEE 1800-2023 §6.3.2) ---

enum class Strength : uint8_t {
    Highz = 0,
    Small = 1,
    Medium = 2,
    Weak = 3,
    Large = 4,
    Pull = 5,
    Strong = 6,
    Supply = 7,
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

// --- Event scheduler regions (IEEE 1800-2023 §4.4) ---

enum class Region : uint8_t {
    Preponed,
    PreActive,
    Active,
    Inactive,
    PreNBA,
    NBA,
    PostNBA,
    PreObserved,
    Observed,
    PostObserved,
    Reactive,
    ReInactive,
    PreReNBA,
    ReNBA,
    PostReNBA,
    PrePostponed,
    Postponed,
    COUNT
};

static constexpr size_t kRegionCount = static_cast<size_t>(Region::COUNT);

// --- Net types (IEEE 1800-2023 §6.5) ---

enum class NetType : uint8_t {
    Wire,
    Tri,
    Wand,
    Triand,
    Wor,
    Trior,
    Tri0,
    Tri1,
    Supply0,
    Supply1,
    Trireg,
    Uwire,
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
            spill_to_heap();
        }
        heap_.push_back(val);
        ++size_;
    }

    T& operator[](size_t i) {
        return (size_ <= N) ? inline_[i] : heap_[i];
    }

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
    void spill_to_heap() {
        heap_.reserve(N * 2);
        for (size_t i = 0; i < N; ++i) {
            heap_.push_back(inline_[i]);
        }
    }

    size_t size_ = 0;
    std::array<T, N> inline_{};
    std::vector<T> heap_;
};

} // namespace delta
