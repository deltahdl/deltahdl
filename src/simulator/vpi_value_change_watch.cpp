#include "simulator/vpi_value_change_watch.h"

#include <algorithm>
#include <cstdint>
#include <utility>
#include <vector>

#include "common/types.h"
#include "simulator/net.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

bool IsPlacedOn(const std::vector<s_cb_data>& callbacks, int reason,
                const VpiObject* obj) {
  return std::ranges::any_of(callbacks, [reason, obj](const s_cb_data& cb) {
    return cb.reason == reason && VpiObjectOf(cb.obj) == obj;
  });
}

std::vector<uint64_t> ObjectBits(const VpiObject& obj) {
  const Logic4Vec& whole = obj.var->value;
  std::vector<uint64_t> bits;
  if (obj.bit_offset < 0) {
    for (uint32_t i = 0; i < whole.nwords; ++i) {
      bits.push_back(whole.words[i].aval);
      bits.push_back(whole.words[i].bval);
    }
    return bits;
  }
  const auto kFirst = static_cast<uint32_t>(obj.bit_offset);
  const uint32_t kEnd = std::min(
      kFirst + static_cast<uint32_t>(std::max(obj.size, 1)), whole.width);
  for (uint32_t bit = kFirst; bit < kEnd; ++bit) {
    bits.push_back((whole.words[bit / 64].aval >> (bit % 64)) & 1);
    bits.push_back((whole.words[bit / 64].bval >> (bit % 64)) & 1);
  }
  return bits;
}

}  // namespace

NetStrength StrengthOf(const VpiObject& obj) {
  return obj.net != nullptr ? obj.net->resolved_strength : NetStrength{};
}

void NoteValueChange(VpiContext& vpi, VpiObject* obj,
                     std::vector<uint64_t>& held, NetStrength& strength,
                     bool call_back) {
  std::vector<uint64_t> now = ObjectBits(*obj);
  const NetStrength kStrength = StrengthOf(*obj);
  const bool kValueChanged = now != held;
  const bool kStrengthChanged = kStrength != strength;
  held = std::move(now);
  strength = kStrength;
  if (!call_back) return;
  if (kValueChanged) {
    vpi.DispatchCallbacks(cbValueChange, obj);
  } else if (kStrengthChanged) {
    vpi.DispatchStrengthChange(obj);
  }
}

void WatchObjectChanges(VpiContext& vpi, VpiObject* obj) {
  if (obj->var == nullptr || obj->value_change_watched) return;
  obj->value_change_watched = true;
  obj->var->AddWatcher([&vpi, obj, held = ObjectBits(*obj),
                        strength = StrengthOf(*obj),
                        size = vpi.Get(vpiSize, obj)]() mutable {
    const auto& callbacks = vpi.RegisteredCallbacks();
    const bool kSizes = IsPlacedOn(callbacks, cbSizeChange, obj);
    const bool kValues = IsPlacedOn(callbacks, cbValueChange, obj);
    if (!kSizes && !kValues) {
      obj->value_change_watched = false;
      return true;
    }
    const int kSize = vpi.Get(vpiSize, obj);
    if (kSize != size) {
      size = kSize;
      if (kSizes) vpi.DispatchCallbacks(cbSizeChange, obj);
    }
    NoteValueChange(vpi, obj, held, strength, kValues);
    return false;
  });
}

}  // namespace delta
