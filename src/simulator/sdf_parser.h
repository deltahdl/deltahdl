#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "parser/ast.h"

namespace delta {

class SpecifyManager;

// =============================================================================
// SDF data structures (IEEE 1800-2023 §32, IEEE 1497-2001)
// =============================================================================

struct SdfDelayValue {
  uint64_t min_val = 0;
  uint64_t typ_val = 0;
  uint64_t max_val = 0;
};

struct SdfIopath {
  std::string src_port;
  std::string dst_port;
  SdfDelayValue rise;
  SdfDelayValue fall;
  SdfDelayValue turnoff;
  bool is_increment = false;
};

enum class SdfCheckType : uint8_t {
  kSetup,
  kHold,
  kSetuphold,
  kRecovery,
  kRemoval,
  kRecrem,
  kWidth,
  kPeriod,
  kSkew,
  kNochange,
};

struct SdfTimingCheck {
  SdfCheckType check_type = SdfCheckType::kSetup;
  std::string ref_port;
  SpecifyEdge ref_edge = SpecifyEdge::kNone;
  std::string data_port;
  SpecifyEdge data_edge = SpecifyEdge::kNone;
  SdfDelayValue limit;
  SdfDelayValue limit2;  // For setuphold/recrem
};

// §32.2: SDF specparam value update. Carries the new value the SDF file
// supplies for a SystemVerilog specparam. The detailed mapping from SDF's
// LABEL section to this struct is §32.4's responsibility; the §32.2
// contract is just that backannotation can carry such a value through.
struct SdfSpecparam {
  std::string name;
  SdfDelayValue value;
};

// §32.2: SDF interconnect delay between two ports. Same split: §32.4 owns
// the INTERCONNECT/PORT parsing, §32.2 owns the fact that backannotation
// names interconnect delays as one of its four update categories.
struct SdfInterconnect {
  std::string src_port;
  std::string dst_port;
  SdfDelayValue rise;
  SdfDelayValue fall;
};

struct SdfCell {
  std::string cell_type;
  std::string instance;
  std::vector<SdfIopath> iopaths;
  std::vector<SdfTimingCheck> timing_checks;
  // §32.2's two remaining backannotation categories. Empty by default so
  // existing IOPATH/TIMINGCHECK-only flows keep observing zero specparams
  // and zero interconnects.
  std::vector<SdfSpecparam> specparams;
  std::vector<SdfInterconnect> interconnects;
};

struct SdfFile {
  std::string version;
  std::string design;
  std::vector<SdfCell> cells;
};

// Min/typ/max selection mode (§32.9).
enum class SdfMtm : uint8_t {
  kMinimum,
  kTypical,
  kMaximum,
};

// =============================================================================
// SDF parser
// =============================================================================

// Parse an SDF string into an SdfFile structure.
bool ParseSdf(std::string_view input, SdfFile& out);

// =============================================================================
// Delay expansion (Table 32-4)
// =============================================================================

// Expand 1/2/3/6/12 delay values into 12 transition delays.
std::vector<uint64_t> ExpandSdfDelays(const std::vector<SdfDelayValue>& vals,
                                      SdfMtm mtm);

// =============================================================================
// SDF annotation
// =============================================================================

// Apply parsed SDF data to a SpecifyManager.
void AnnotateSdfToManager(const SdfFile& file, SpecifyManager& mgr, SdfMtm mtm);

}  // namespace delta
