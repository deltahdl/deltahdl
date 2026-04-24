#pragma once

#include <cstdint>

#include "model_val4.h"

// --- Local types for MOS/pass switches (§28.7, §28.8, §28.9) ---

enum class Val4Ext : uint8_t {
  kV0 = 0,
  kV1 = 1,
  kX = 2,
  kZ = 3,
  kL = 4,
  kH = 5
};

enum class SwitchType : uint8_t {
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
};

inline Val4Ext EvalMosSwitch(SwitchType type, Val4 data, Val4 control);
inline bool IsBidirectional(SwitchType type);
inline bool AcceptsDelaySpec(SwitchType type);
inline uint32_t MaxSwitchDelays(SwitchType type);

// §28.8: A bidirectional pass-enable switch's optional delay spec carries up
// to two values that constrain only the control input (turn-on/turn-off).
// Stored as two optional values so the helpers below can apply the LRM rules
// for the 0/1/2-delay forms without re-deriving structure.
struct PassSwitchDelaySpec {
  bool has_first = false;
  bool has_second = false;
  uint64_t first = 0;
  uint64_t second = 0;
};

inline uint64_t EffectiveTurnOnDelay(const PassSwitchDelaySpec& spec);
inline uint64_t EffectiveTurnOffDelay(const PassSwitchDelaySpec& spec);
inline uint64_t EffectiveBuiltinControlXZDelay(
    const PassSwitchDelaySpec& spec);

// --- Implementations ---
inline Val4Ext EvalMosSwitch(SwitchType type, Val4 data, Val4 control) {
  if (data == Val4::kZ) return Val4Ext::kZ;

  bool complementary =
      (type == SwitchType::kPmos || type == SwitchType::kRpmos);

  Val4 eff = control;
  if (complementary) {
    switch (control) {
      case Val4::kV0:
        eff = Val4::kV1;
        break;
      case Val4::kV1:
        eff = Val4::kV0;
        break;
      default:
        eff = control;
        break;
    }
  }

  switch (eff) {
    case Val4::kV1:
      switch (data) {
        case Val4::kV0:
          return Val4Ext::kV0;
        case Val4::kV1:
          return Val4Ext::kV1;
        case Val4::kX:
          return Val4Ext::kX;
        case Val4::kZ:
          return Val4Ext::kZ;
      }
      break;
    case Val4::kV0:
      return Val4Ext::kZ;
    case Val4::kX:
    case Val4::kZ:
      switch (data) {
        case Val4::kV0:
          return Val4Ext::kL;
        case Val4::kV1:
          return Val4Ext::kH;
        case Val4::kX:
          return Val4Ext::kX;
        case Val4::kZ:
          return Val4Ext::kZ;
      }
      break;
  }
  return Val4Ext::kX;
}

inline bool IsBidirectional(SwitchType type) {
  switch (type) {
    case SwitchType::kTran:
    case SwitchType::kRtran:
    case SwitchType::kTranif0:
    case SwitchType::kTranif1:
    case SwitchType::kRtranif0:
    case SwitchType::kRtranif1:
      return true;
    default:
      return false;
  }
}

inline bool AcceptsDelaySpec(SwitchType type) {
  switch (type) {
    case SwitchType::kTran:
    case SwitchType::kRtran:
      return false;
    default:
      return true;
  }
}

inline uint32_t MaxSwitchDelays(SwitchType type) {
  switch (type) {
    case SwitchType::kTran:
    case SwitchType::kRtran:
      return 0;
    case SwitchType::kTranif0:
    case SwitchType::kTranif1:
    case SwitchType::kRtranif0:
    case SwitchType::kRtranif1:
      return 2;
    case SwitchType::kNmos:
    case SwitchType::kPmos:
    case SwitchType::kRnmos:
    case SwitchType::kRpmos:
    case SwitchType::kCmos:
    case SwitchType::kRcmos:
      return 3;
  }
  return 0;
}

// §28.8: With two delays the first selects turn-on; with one delay that single
// value applies to both turn-on and turn-off; with no delay there is no
// turn-on delay.
inline uint64_t EffectiveTurnOnDelay(const PassSwitchDelaySpec& spec) {
  return spec.has_first ? spec.first : 0;
}

// §28.8: Mirror of EffectiveTurnOnDelay — the second delay drives turn-off
// when present, otherwise the single delay applies to both edges.
inline uint64_t EffectiveTurnOffDelay(const PassSwitchDelaySpec& spec) {
  if (spec.has_second) return spec.second;
  if (spec.has_first) return spec.first;
  return 0;
}

// §28.8: For bidirectional switches connecting built-in net types, control
// input transitions to x and z take the smaller of the two delays. With one
// delay both edges share that value, so the same rule collapses to it.
inline uint64_t EffectiveBuiltinControlXZDelay(
    const PassSwitchDelaySpec& spec) {
  if (spec.has_second)
    return spec.first < spec.second ? spec.first : spec.second;
  if (spec.has_first) return spec.first;
  return 0;
}
