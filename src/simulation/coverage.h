#pragma once

#include <cstdint>
#include <deque>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

namespace delta {

// =============================================================================
// §19.5: Cover bin types
// =============================================================================

enum class CoverBinKind : uint8_t {
  kExplicit,    // bins name = {values}
  kAuto,        // Automatically generated bins
  kTransition,  // bins name = (val1 => val2 => ...)
  kWildcard,    // wildcard bins name = {values with ?/x}
  kIllegal,     // illegal_bins name = {values}
  kIgnore,      // ignore_bins name = {values}
};

// =============================================================================
// §19.5: CoverBin: a single bin within a coverpoint
// =============================================================================

struct CoverBin {
  std::string name;
  CoverBinKind kind = CoverBinKind::kExplicit;
  std::vector<int64_t> values;
  std::vector<std::vector<int64_t>> transitions;
  uint64_t hit_count = 0;
  uint32_t at_least = 1;  // §19.7: minimum hit count for covered status
};

// =============================================================================
// §19.5: CoverPoint: a coverpoint within a covergroup
// =============================================================================

struct CoverPoint {
  std::string name;
  std::vector<CoverBin> bins;
  bool has_iff_guard = false;
  bool iff_guard_value = true;
  int64_t auto_bin_min = 0;
  int64_t auto_bin_max = 0;
  uint32_t auto_bin_count = 64;  // §19.7: default auto_bin_max
};

// =============================================================================
// §19.6: CrossCover: cross coverage between coverpoints
// =============================================================================

struct CrossBin {
  std::string name;
  std::vector<std::vector<int64_t>> value_sets;  // One set per crossed point.
  uint64_t hit_count = 0;
  uint32_t at_least = 1;
};

struct CrossCover {
  std::string name;
  std::vector<std::string> coverpoint_names;
  std::vector<CrossBin> bins;
};

// =============================================================================
// §19.7: Coverage options
// =============================================================================

struct CoverOptions {
  uint32_t at_least = 1;
  uint32_t weight = 1;
  double goal = 100.0;
  uint32_t auto_bin_max = 64;
};

// =============================================================================
// §19.2-19.3: CoverGroup: a covergroup definition
// =============================================================================

struct CoverGroup {
  std::string name;
  std::vector<CoverPoint> coverpoints;
  std::vector<CrossCover> crosses;
  CoverOptions options;
  uint64_t sample_count = 0;
};

// =============================================================================
// §19.8-19.9: CoverageDB: global coverage database
// =============================================================================

class CoverageDB {
 public:
  CoverGroup* CreateGroup(std::string name);
  CoverGroup* FindGroup(std::string_view name);
  uint32_t GroupCount() const;

  // §19.5: Coverpoint operations.
  static CoverPoint* AddCoverPoint(CoverGroup* group, std::string name);
  static CoverBin* AddBin(CoverPoint* cp, CoverBin bin);

  // §19.5.1-19.5.3: Auto bin creation.
  static void AutoCreateBins(CoverPoint* cp, int64_t min_val, int64_t max_val);

  // §19.6: Cross coverage.
  static CrossCover* AddCross(CoverGroup* group, CrossCover cross);

  // §19.8: Sample a covergroup with given values.
  void Sample(CoverGroup* group,
              const std::vector<std::pair<std::string, int64_t>>& values);

  // §19.8: Coverage computation.
  static double GetCoverage(const CoverGroup* group);
  static double GetInstCoverage(const CoverGroup* group);
  static double GetPointCoverage(const CoverPoint* cp);
  static double GetCrossCoverage(const CrossCover* cross);

  // §19.9: Global $get_coverage().
  double GetGlobalCoverage() const;

 private:
  void SampleCoverPoint(CoverPoint* cp, int64_t value);
  void SampleCross(CrossCover* cross,
                   const std::vector<std::pair<std::string, int64_t>>& vals);

  std::deque<CoverGroup> groups_;
  std::unordered_map<std::string, size_t> name_index_;
};

}  // namespace delta
