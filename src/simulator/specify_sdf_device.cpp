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

void ApplySdfDeviceValues(uint64_t (&slots)[12], const SdfDeviceAnnotation& a) {
  for (std::size_t i = 0; i < 12; ++i) {
    if (a.held[i]) continue;
    slots[i] = a.is_increment ? slots[i] + a.delays[i] : a.delays[i];
  }
}

constexpr int kSlotsReachingX[3] = {6, 8, 11};

void ApplySdfDeviceThreeStateValues(PrimitiveDriver& driver,
                                    const SdfDeviceAnnotation& a) {
  PathDelay scratch;
  scratch.delay_count = 3;
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

struct SdfDeviceTarget {
  std::string inst_prefix;
  std::string output;
};

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
  const SdfDeviceTarget kTarget = ResolveSdfDeviceTarget(
      inst_prefix, a.port_instance, path_delays_, primitive_drivers_);
  return AnnotateSdfDevicePaths(path_delays_, a, kTarget, reject_pulse_pct_,
                                error_pulse_pct_) ||
         AnnotateSdfDevicePrimitives(primitive_drivers_, a, kTarget);
}

}  // namespace delta
