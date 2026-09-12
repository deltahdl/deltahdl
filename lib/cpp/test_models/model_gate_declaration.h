#pragma once

#include <cstdint>
#include <cstdlib>

// --- Local types for gate declaration (§28.3) ---
enum class ModelGateType : uint8_t {
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
  ModelGateType type = ModelGateType::kAnd;
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

inline bool CanHaveStrengthSpec(ModelGateType type);

inline uint32_t ComputeArraySize(int32_t lhi, int32_t rhi);

inline bool ValidateStrengthSpec(StrengthLvl s0, StrengthLvl s1,
                                 ModelGateType type);

inline uint32_t MaxDelays(ModelGateType type);

inline bool ValidateGateDecl(const GateDeclInfo& info) {
  return !info.has_range || info.has_name;
}

inline bool CanHaveStrengthSpec(ModelGateType type) {
  switch (type) {
    case ModelGateType::kAnd:
    case ModelGateType::kNand:
    case ModelGateType::kOr:
    case ModelGateType::kNor:
    case ModelGateType::kXor:
    case ModelGateType::kXnor:
    case ModelGateType::kBuf:
    case ModelGateType::kNot:
    case ModelGateType::kBufif0:
    case ModelGateType::kBufif1:
    case ModelGateType::kNotif0:
    case ModelGateType::kNotif1:
    case ModelGateType::kPullup:
    case ModelGateType::kPulldown:
      return true;
    case ModelGateType::kNmos:
    case ModelGateType::kPmos:
    case ModelGateType::kRnmos:
    case ModelGateType::kRpmos:
    case ModelGateType::kTran:
    case ModelGateType::kRtran:
    case ModelGateType::kTranif0:
    case ModelGateType::kTranif1:
    case ModelGateType::kRtranif0:
    case ModelGateType::kRtranif1:
    case ModelGateType::kCmos:
    case ModelGateType::kRcmos:
      return false;
  }
  return false;
}

inline uint32_t ComputeArraySize(int32_t lhi, int32_t rhi) {
  return static_cast<uint32_t>(std::abs(lhi - rhi)) + 1;
}

inline bool ValidateStrengthSpec(StrengthLvl s0, StrengthLvl s1,
                                 ModelGateType /*type*/) {
  return s0 != StrengthLvl::kHighz || s1 != StrengthLvl::kHighz;
}

inline uint32_t MaxDelays(ModelGateType type) {
  switch (type) {
    case ModelGateType::kPullup:
    case ModelGateType::kPulldown:
      return 0;
    case ModelGateType::kAnd:
    case ModelGateType::kNand:
    case ModelGateType::kOr:
    case ModelGateType::kNor:
    case ModelGateType::kXor:
    case ModelGateType::kXnor:
    case ModelGateType::kBuf:
    case ModelGateType::kNot:
      return 2;
    case ModelGateType::kBufif0:
    case ModelGateType::kBufif1:
    case ModelGateType::kNotif0:
    case ModelGateType::kNotif1:
    case ModelGateType::kNmos:
    case ModelGateType::kPmos:
    case ModelGateType::kRnmos:
    case ModelGateType::kRpmos:
    case ModelGateType::kCmos:
    case ModelGateType::kRcmos:
      return 3;
    case ModelGateType::kTranif0:
    case ModelGateType::kTranif1:
    case ModelGateType::kRtranif0:
    case ModelGateType::kRtranif1:
      return 2;
    case ModelGateType::kTran:
    case ModelGateType::kRtran:
      return 0;
  }
  return 0;
}
