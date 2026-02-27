#pragma once

#include <cstdint>

// --- Local types for MOS/pass switches (§28.7, §28.8, §28.9) ---
enum class Val4 : uint8_t { kV0 = 0, kV1 = 1, kX = 2, kZ = 3 };

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
