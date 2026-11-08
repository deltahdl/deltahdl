#pragma once

#include <string_view>
#include <unordered_map>

namespace delta {

struct RsProductionItem;

struct RuleValueCapture {
  std::unordered_map<std::string_view, int> total;
  std::unordered_map<const RsProductionItem*, int> ordinal;
};

struct RuleProductionSlot {
  std::string_view name;
  int idx;
  int total;
};

}  // namespace delta
