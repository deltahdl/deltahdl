#include "simulator/vpi_put_run_delays.h"

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_timing_check.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_primitive_value.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// The delays `obj` holds now, in simulation ticks.
std::vector<uint64_t> TicksOf(const VpiObject& obj) {
  std::vector<uint64_t> ticks;
  ticks.reserve(obj.delays.size());
  for (const VpiDelayInfo& delay : obj.delays) {
    ticks.push_back(static_cast<uint64_t>(std::llround(delay.delay)));
  }
  return ticks;
}

// §30.5.1 with §38.32: the module path's new delays, distributed over its
// transitions as a declaration listing as many is.
void PutPathDelays(PathDelay& path, const std::vector<uint64_t>& ticks) {
  const std::size_t kCount = std::min<std::size_t>(ticks.size(), 12);
  for (std::size_t i = 0; i < kCount; ++i) path.delays[i] = ticks[i];
  path.delay_count = static_cast<uint8_t>(kCount);
  ExpandTransitionDelays(path);
}

// §28.16 with §38.32: the gate's or udp's new rise, fall and turn-off
// delays, a turn-off it was given none of being the lesser of the other two,
// filed with the primitive driving its output, below the instance its run key
// names.
void PutPrimitiveDelays(VpiObject& prim, const std::vector<uint64_t>& ticks,
                        SimContext& sim) {
  const VpiObject* output = VpiPrimitiveValueSource(&prim);
  if (output == nullptr || ticks.empty()) return;
  const std::string_view kOutput =
      output->name.substr(0, output->name.find('['));
  const std::size_t kDot = prim.run_key.rfind('.');
  const std::string kPrefix =
      kDot == std::string::npos ? "" : prim.run_key.substr(0, kDot + 1);
  uint64_t delays[3] = {ticks[0], ticks.size() > 1 ? ticks[1] : ticks[0], 0};
  delays[2] = ticks.size() > 2 ? ticks[2] : std::min(delays[0], delays[1]);
  sim.AcquireSpecifyManager().AnnotateDriverDelays(kPrefix, kOutput, delays);
}

}  // namespace

void VpiPutRunDelays(
    VpiObject& obj,
    const std::unordered_map<const VpiObject*, std::size_t>& run_entries,
    SimContext& sim) {
  const std::vector<uint64_t> kTicks = TicksOf(obj);
  if (VpiIsPrimitiveType(obj.type) && !obj.run_key.empty()) {
    PutPrimitiveDelays(obj, kTicks, sim);
    return;
  }
  const auto kEntry = run_entries.find(&obj);
  if (kEntry == run_entries.end()) return;
  SpecifyManager& specify = sim.AcquireSpecifyManager();
  if (obj.type == vpiModPath) {
    PutPathDelays(specify.MutablePathDelays()[kEntry->second], kTicks);
    return;
  }
  // §31.2 with §38.32: a timing check's limits, the first and, for a check
  // taking two, the second.
  TimingCheckEntry& check = specify.MutableTimingChecks()[kEntry->second];
  if (!kTicks.empty()) check.limit = kTicks[0];
  if (kTicks.size() > 1) check.limit2 = kTicks[1];
}

}  // namespace delta
