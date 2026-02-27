#pragma once

#include <cstdint>
#include <cstdlib>

// --- Local types for gate declaration (§28.3) ---
enum class GateType : uint8_t {
  kAnd,
  kNand,
  kOr,
  kNor,
  kXor,
  kXnor,
  kBuf,
  kNot,
  kBufif0,
  kBufif1,
  kNotif0,
  kNotif1,
  kNmos,
  kPmos,
  kRnmos,
  kRpmos,
  kTran,
  kRtran,
  kTranif0,
  kTranif1,
  kRtranif0,
  kRtranif1,
  kCmos,
  kRcmos,
  kPullup,
  kPulldown,
};

enum class StrengthLvl : uint8_t {
  kHighz = 0,
  kSmall,
  kMedium,
  kWeak,
  kLarge,
  kPull,
  kStrong,
  kSupply
};

struct GateDeclInfo {
  GateType type = GateType::kAnd;
  bool has_strength = false;
  StrengthLvl strength0 = StrengthLvl::kStrong;
  StrengthLvl strength1 = StrengthLvl::kStrong;
  uint32_t delay_count = 0;
  bool has_name = false;
  bool has_range = false;
  int32_t range_lhi = 0;
  int32_t range_rhi = 0;
  uint32_t terminal_count = 0;
};

inline bool ValidateGateDecl(const GateDeclInfo& info);

inline bool CanHaveStrengthSpec(GateType type);

inline uint32_t ComputeArraySize(int32_t lhi, int32_t rhi);

inline bool ValidateStrengthSpec(StrengthLvl s0, StrengthLvl s1, GateType type);

inline uint32_t MaxDelays(GateType type);

inline bool ValidateGateDecl(const GateDeclInfo& info) {
  return !info.has_range || info.has_name;
}

inline bool CanHaveStrengthSpec(GateType type) {
  switch (type) {
    case GateType::kAnd:
    case GateType::kNand:
    case GateType::kOr:
    case GateType::kNor:
    case GateType::kXor:
    case GateType::kXnor:
    case GateType::kBuf:
    case GateType::kNot:
    case GateType::kBufif0:
    case GateType::kBufif1:
    case GateType::kNotif0:
    case GateType::kNotif1:
    case GateType::kPullup:
    case GateType::kPulldown:
      return true;
    case GateType::kNmos:
    case GateType::kPmos:
    case GateType::kRnmos:
    case GateType::kRpmos:
    case GateType::kTran:
    case GateType::kRtran:
    case GateType::kTranif0:
    case GateType::kTranif1:
    case GateType::kRtranif0:
    case GateType::kRtranif1:
    case GateType::kCmos:
    case GateType::kRcmos:
      return false;
  }
  return false;
}

inline uint32_t ComputeArraySize(int32_t lhi, int32_t rhi) {
  return static_cast<uint32_t>(std::abs(lhi - rhi)) + 1;
}

inline bool ValidateStrengthSpec(StrengthLvl s0, StrengthLvl s1, GateType /*type*/) {
  return s0 != StrengthLvl::kHighz || s1 != StrengthLvl::kHighz;
}

inline uint32_t MaxDelays(GateType type) {
  switch (type) {
    case GateType::kPullup:
    case GateType::kPulldown:
      return 0;
    case GateType::kAnd:
    case GateType::kNand:
    case GateType::kOr:
    case GateType::kNor:
    case GateType::kXor:
    case GateType::kXnor:
    case GateType::kBuf:
    case GateType::kNot:
      return 2;
    case GateType::kBufif0:
    case GateType::kBufif1:
    case GateType::kNotif0:
    case GateType::kNotif1:
    case GateType::kNmos:
    case GateType::kPmos:
    case GateType::kRnmos:
    case GateType::kRpmos:
    case GateType::kCmos:
    case GateType::kRcmos:
      return 3;
    case GateType::kTranif0:
    case GateType::kTranif1:
    case GateType::kRtranif0:
    case GateType::kRtranif1:
      return 2;
    case GateType::kTran:
    case GateType::kRtran:
      return 0;
  }
  return 0;
}
