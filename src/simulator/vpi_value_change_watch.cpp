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

// §38.36.1: whether a `reason` registration placed on `obj` is still live
// among `callbacks`.
bool IsPlacedOn(const std::vector<s_cb_data>& callbacks, int reason,
                const VpiObject* obj) {
  // `obj` is the object watched, never null, so a registration with no object
  // matches none.
  return std::ranges::any_of(callbacks, [reason, obj](const s_cb_data& cb) {
    return cb.reason == reason && VpiObjectOf(cb.obj) == obj;
  });
}

// The aval and bval words of the bits `obj` stands for: its variable's, or,
// for a bit or a select of one, those of its parent's it spans, up to the
// variable's last bit.
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

// §38.36.1 with §37.17 detail 14: watch the storage of `obj` and, as it is
// written, call back the cbSizeChange registrations placed on it where its
// size changed, then the cbValueChange ones where its value did, a write of
// what it holds being no change, until none of either is left.
// The strength the net `obj` reads, or none for an object without one.
NetStrength StrengthOf(const VpiObject& obj) {
  return obj.net != nullptr ? obj.net->resolved_strength : NetStrength{};
}

// §38.36.1: what `obj` holds now against the bits `held` and the strength
// `strength` last seen, both brought up to date, and, where `call_back`, its
// cbValueChange callbacks called for a change of value or, a change of
// strength alone being a change to a vpiStrengthVal callback and to no other,
// of strength.
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
  // Its one caller, vpi_register_cb, passes a registration's object only.
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
