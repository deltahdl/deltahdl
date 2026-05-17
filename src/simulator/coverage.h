#pragma once

#include <cstdint>
#include <deque>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

namespace delta {

enum class CoverBinKind : uint8_t {
  kExplicit,
  kAuto,
  kTransition,
  kWildcard,
  kIllegal,
  kIgnore,
};

struct CoverBin {
  std::string name;
  CoverBinKind kind = CoverBinKind::kExplicit;
  std::vector<int64_t> values;
  std::vector<std::vector<int64_t>> transitions;
  uint64_t hit_count = 0;
  uint32_t at_least = 1;
};

struct CoverPoint {
  std::string name;
  std::vector<CoverBin> bins;
  bool has_iff_guard = false;
  bool iff_guard_value = true;
  int64_t auto_bin_min = 0;
  int64_t auto_bin_max = 0;
  uint32_t auto_bin_count = 64;
};

struct CrossBin {
  std::string name;
  std::vector<std::vector<int64_t>> value_sets;
  uint64_t hit_count = 0;
  uint32_t at_least = 1;
};

struct CrossCover {
  std::string name;
  std::vector<std::string> coverpoint_names;
  std::vector<CrossBin> bins;
};

struct CoverOptions {
  uint32_t at_least = 1;
  uint32_t weight = 1;
  double goal = 100.0;
  uint32_t auto_bin_max = 64;
};

struct CoverGroup {
  std::string name;
  std::vector<CoverPoint> coverpoints;
  std::vector<CrossCover> crosses;
  CoverOptions options;
  uint64_t sample_count = 0;
};

class CoverageDB {
 public:
  CoverGroup* CreateGroup(std::string name);
  CoverGroup* FindGroup(std::string_view name);
  uint32_t GroupCount() const;

  static CoverPoint* AddCoverPoint(CoverGroup* group, std::string name);
  static CoverBin* AddBin(CoverPoint* cp, CoverBin bin);

  static void AutoCreateBins(CoverPoint* cp, int64_t min_val, int64_t max_val);

  static CrossCover* AddCross(CoverGroup* group, CrossCover cross);

  void Sample(CoverGroup* group,
              const std::vector<std::pair<std::string, int64_t>>& values);

  static double GetCoverage(const CoverGroup* group);
  static double GetInstCoverage(const CoverGroup* group);
  static double GetPointCoverage(const CoverPoint* cp);
  static double GetCrossCoverage(const CrossCover* cross);

  double GetGlobalCoverage() const;

 private:
  void SampleCoverPoint(CoverPoint* cp, int64_t value);
  void SampleCross(CrossCover* cross,
                   const std::vector<std::pair<std::string, int64_t>>& vals);

  std::deque<CoverGroup> groups_;
  std::unordered_map<std::string, size_t> name_index_;
};

}
