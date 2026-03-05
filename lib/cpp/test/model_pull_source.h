#pragma once

#include "model_strength.h"
#include "model_val4.h"

// --- Local types for pullup/pulldown sources (§28.10) ---

enum class PullKind : uint8_t { kPullup, kPulldown };

struct PullSourceInfo {
  PullKind kind = PullKind::kPullup;
  bool has_strength0 = false;
  bool has_strength1 = false;
  StrengthLevel strength0 = StrengthLevel::kPull;
  StrengthLevel strength1 = StrengthLevel::kPull;
};

inline Val4 EvalPullSource(PullKind kind) {
  return kind == PullKind::kPullup ? Val4::kV1 : Val4::kV0;
}

inline StrengthLevel GetPullSourceStrength(const PullSourceInfo& info) {
  if (info.kind == PullKind::kPullup) {
    // For pullup, only strength1 is relevant; strength0 is ignored.
    return info.has_strength1 ? info.strength1 : StrengthLevel::kPull;
  }
  // For pulldown, only strength0 is relevant; strength1 is ignored.
  return info.has_strength0 ? info.strength0 : StrengthLevel::kPull;
}

inline bool PullSourceAcceptsDelaySpec() { return false; }
