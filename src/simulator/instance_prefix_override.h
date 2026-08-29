#pragma once

// §32.4.3: the instance an evaluation stands in, where that is not the instance
// of whatever process is running.
//
// SimContext resolves a name written without a hierarchical path by joining it
// to the running process's instance prefix, which is right for anything the
// process itself wrote. It is wrong for a rebuild. When an SDF LABEL annotates
// a specparam, SpecifyManager recomputes every module path delay that reads it
// from the declaration, and that declaration belongs to the instance that
// registered it rather than to the process that ran $sdf_annotate. Without an
// override the rebuild reads the caller's specparam of that name, or finds none
// and folds the delay to zero, so a LABEL naming a cell's specparam writes the
// right value into the right place and then rebuilds the path from the wrong
// one.
//
// The state lives on SimContext because ActiveInstancePrefix is what reads it.
// It stands here so that neither of them has to know about the other.

#include <string>
#include <string_view>
#include <utility>

namespace delta {

// Whether an override is in force and the prefix it names, ending in a `.` and
// empty for the module the design was elaborated as.
struct InstancePrefixOverrideState {
  bool active = false;
  std::string prefix;
};

// Holds an override for one evaluation and restores whatever it found.
// DelayModeGuard in src/elaborator/const_eval.h is the same shape for §11.11's
// min:typ:max selection.
class InstancePrefixOverride {
 public:
  InstancePrefixOverride(InstancePrefixOverrideState& state,
                         std::string_view prefix)
      : state_(state), saved_(state) {
    state_.active = true;
    state_.prefix = std::string(prefix);
  }

  ~InstancePrefixOverride() { state_ = std::move(saved_); }

  InstancePrefixOverride(const InstancePrefixOverride&) = delete;
  InstancePrefixOverride& operator=(const InstancePrefixOverride&) = delete;

 private:
  InstancePrefixOverrideState& state_;
  InstancePrefixOverrideState saved_;
};

}  // namespace delta
