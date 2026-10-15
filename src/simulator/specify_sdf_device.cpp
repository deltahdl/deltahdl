// §32.4.1's DEVICE construct and §32.8's mapping of its values: an SDF DEVICE
// entry reaches the specify paths to a module's outputs, or, where none covers
// them, the primitives driving those outputs, which carry three state
// transition delays rather than twelve.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/specify.h"
#include "simulator/specify_internal.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_sdf.h"

namespace delta {

namespace {

// Writes an SDF DEVICE entry's twelve values over `slots`, or adds them to what
// is there when the entry came from an INCREMENT delay section.
void ApplySdfDeviceValues(uint64_t (&slots)[12], const SdfDeviceAnnotation& a) {
  for (std::size_t i = 0; i < 12; ++i) {
    if (a.held[i]) continue;
    slots[i] = a.is_increment ? slots[i] + a.delays[i] : a.delays[i];
  }
}

// §32.8: the transition slots whose transition ends at the x state -- 0 to x,
// 1 to x and z to x. A construct that carries only three state transition
// delays has a single delay to the x state, so all three take the same value.
constexpr int kSlotsReachingX[3] = {6, 8, 11};

// §32.8: write an SDF DEVICE entry onto a gate primitive, which is one of the
// constructs that carries three state transition delays rather than twelve. The
// three the entry reduced to spread over the slots the way a three-delay
// declaration spreads, and the delay to the x state -- which the reduction took
// as the smallest of the three -- fills every slot whose transition ends at x,
// in place of whatever that spreading derived there. An INCREMENT entry changes
// what the primitive already carries rather than replacing it, in each of the
// four values it supplies.
void ApplySdfDeviceThreeStateValues(PrimitiveDriver& driver,
                                    const SdfDeviceAnnotation& a) {
  PathDelay scratch;
  scratch.delay_count = 3;
  // §32.5: a delay the entry wrote empty keeps what the primitive carries.
  for (std::size_t i = 0; i < 3; ++i) {
    scratch.delays[i] = a.three_state_held[i] ? driver.delays[i]
                        : a.is_increment
                            ? driver.delays[i] + a.three_state_delays[i]
                            : a.three_state_delays[i];
  }
  ExpandTransitionDelays(scratch);

  uint64_t to_x = a.three_state_delays[3];
  if (a.is_increment) to_x += driver.delays[kSlotsReachingX[0]];
  if (a.three_state_held[3]) to_x = driver.delays[kSlotsReachingX[0]];
  for (int slot : kSlotsReachingX) scratch.delays[slot] = to_x;

  driver.delay_count = 3;
  for (int i = 0; i < 12; ++i) driver.delays[i] = scratch.delays[i];
  driver.sdf_annotated = true;
}

}  // namespace

const PrimitiveDriver* SpecifyManager::FindAnnotatedPrimitiveDriver(
    std::string_view inst_prefix, std::string_view output) const {
  for (const auto& driver : primitive_drivers_) {
    if (driver.sdf_annotated && driver.inst_prefix == inst_prefix &&
        driver.output_port == output) {
      return &driver;
    }
  }
  return nullptr;
}

void SpecifyManager::AnnotateDriverDelays(std::string_view inst_prefix,
                                          std::string_view output,
                                          const uint64_t (&delays)[3]) {
  PrimitiveDriver* driver = nullptr;
  for (auto& candidate : primitive_drivers_) {
    if (candidate.inst_prefix == inst_prefix &&
        candidate.output_port == output) {
      driver = &candidate;
      break;
    }
  }
  if (driver == nullptr) {
    driver = &primitive_drivers_.emplace_back();
    driver->inst_prefix = std::string(inst_prefix);
    driver->output_port = std::string(output);
  }
  driver->delay_count = 3;
  for (int i = 0; i < 3; ++i) driver->delays[i] = delays[i];
  driver->sdf_annotated = true;
}

namespace {

// §32.4.1 Table 32-1: where a DEVICE entry's operand leads -- the instance
// whose outputs it reaches, in the form PathDelay::inst_prefix carries, and the
// one output it narrows to, empty for all of them.
struct SdfDeviceTarget {
  std::string inst_prefix;
  std::string output;
};

// The operand names an output of the cell, an instance within it -- `u1`, or
// `u1/u2` further down -- whose every output the entry reaches, or an output
// of such an instance, `u1/y`. An instance is known by the paths or the
// primitive drivers registered under its prefix.
SdfDeviceTarget ResolveSdfDeviceTarget(
    std::string_view cell_prefix, std::string_view operand,
    const std::vector<PathDelay>& paths,
    const std::vector<PrimitiveDriver>& drivers) {
  if (operand.empty()) return {std::string(cell_prefix), {}};
  std::string dotted(operand);
  std::ranges::replace(dotted, '/', '.');
  const std::string kInstance = std::string(cell_prefix) + dotted + ".";
  const bool kIsInstance =
      std::ranges::any_of(
          paths,
          [&](const PathDelay& pd) { return pd.inst_prefix == kInstance; }) ||
      std::ranges::any_of(drivers, [&](const PrimitiveDriver& drv) {
        return drv.inst_prefix == kInstance;
      });
  if (kIsInstance) return {kInstance, {}};
  const std::size_t kDot = dotted.rfind('.');
  if (kDot == std::string::npos) {
    return {std::string(cell_prefix), std::string(operand)};
  }
  return {std::string(cell_prefix) + dotted.substr(0, kDot + 1),
          dotted.substr(kDot + 1)};
}

}  // namespace

namespace {

// The entry onto the specify paths to the outputs `target` names. The
// propagation delays come from the file, and each path keeps its own condition
// and ifnone flag. §32.7: a delay annotated outright brings the pulse limits
// the invocation options' percentages make of it, as an IOPATH's does, in
// place of whatever limits stood; an INCREMENT moves no limit, and a
// transition the entry held keeps both (§32.5).
//
// §30.3 puts a specify block inside a module declaration, so two instances of
// one cell hold outputs spelled identically. The target's prefix is what
// SdfCellPrefixInRegion (simulator/sdf_annotate.cpp) made of the entry's
// CELLINSTANCE, so the scan reaches the outputs of that one instance.
bool AnnotateSdfDevicePaths(std::vector<PathDelay>& paths,
                            const SdfDeviceAnnotation& a,
                            const SdfDeviceTarget& target, uint8_t reject_pct,
                            uint8_t error_pct) {
  bool applied = false;
  for (auto& pd : paths) {
    if (pd.inst_prefix != target.inst_prefix) continue;
    if (!target.output.empty() && pd.dst_port != target.output) continue;
    ApplySdfDeviceValues(pd.delays, a);
    pd.delay_count = 12;
    applied = true;
    if (a.is_increment) continue;
    uint64_t reject[12] = {};
    uint64_t error[12] = {};
    DerivePulseLimitsFromDelays(pd.delays, reject_pct, error_pct, reject,
                                error);
    for (std::size_t i = 0; i < 12; ++i) {
      if (a.held[i]) continue;
      pd.reject_limit[i] = reject[i];
      pd.error_limit[i] = error[i];
    }
    pd.reject_limit_source = PulseLimitSource::kGlobal;
    pd.error_limit_source = PulseLimitSource::kGlobal;
  }
  return applied;
}

// The entry onto the primitives driving the outputs `target` names, where no
// specify path covers them. §32.8: a gate primitive is not a specify path and
// carries three state transition delays rather than twelve, so the entry's
// values reach it through the reduction rather than through the twelve-slot
// expansion the paths take. PrimitiveDriver::inst_prefix is compared for the
// reason PathDelay::inst_prefix is: RegisterModuleGates
// (simulator/specify_register.cpp) fills it, once per module instance.
bool AnnotateSdfDevicePrimitives(std::vector<PrimitiveDriver>& drivers,
                                 const SdfDeviceAnnotation& a,
                                 const SdfDeviceTarget& target) {
  bool applied = false;
  for (auto& driver : drivers) {
    if (driver.inst_prefix != target.inst_prefix) continue;
    if (!driver.drives_module_output) continue;
    if (!target.output.empty() && driver.output_port != target.output) {
      continue;
    }
    ApplySdfDeviceThreeStateValues(driver, a);
    applied = true;
  }
  return applied;
}

}  // namespace

bool SpecifyManager::AnnotateSdfDeviceDelay(const SdfDeviceAnnotation& a,
                                            std::string_view inst_prefix) {
  // An entry with no operand is the whole-module row: it reaches every specify
  // path, because every specify path ends at a module output. An operand naming
  // an instance does the same for that instance, and one naming an output, of
  // the cell or of an instance in it, narrows the entry to it.
  const SdfDeviceTarget kTarget = ResolveSdfDeviceTarget(
      inst_prefix, a.port_instance, path_delays_, primitive_drivers_);
  return AnnotateSdfDevicePaths(path_delays_, a, kTarget, reject_pulse_pct_,
                                error_pulse_pct_) ||
         AnnotateSdfDevicePrimitives(primitive_drivers_, a, kTarget);
}

}  // namespace delta
