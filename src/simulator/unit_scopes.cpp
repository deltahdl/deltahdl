#include "simulator/unit_scopes.h"

#include <cstddef>
#include <string>
#include <string_view>

namespace delta {

namespace {

constexpr std::string_view kUnitScope = "$unit";

}  // namespace

void UnitScopes::SetInstanceUnit(std::string_view inst_prefix, int unit) {
  if (unit < 0) return;
  units_[std::string(inst_prefix)] = unit;
}

int UnitScopes::UnitOf(std::string_view inst_prefix) const {
  // Each prefix ends in a period, so dropping the last name and its period
  // leaves the instance holding this one, down to the empty prefix of the top.
  std::string key(inst_prefix);
  auto it = units_.find(key);
  while (it == units_.end() && !key.empty()) {
    size_t dot = key.find_last_of('.', key.size() - 2);
    key.resize(dot == std::string::npos ? 0 : dot + 1);
    it = units_.find(key);
  }
  return it == units_.end() ? -1 : it->second;
}

std::string UnitScopes::ScopeName(int unit) {
  if (unit < 0) return std::string(kUnitScope);
  return std::string(kUnitScope) + "#" + std::to_string(unit);
}

bool UnitScopes::IsUnitScope(std::string_view name) {
  return name.starts_with(kUnitScope);
}

}  // namespace delta
