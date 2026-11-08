#pragma once

#include <string>
#include <string_view>
#include <unordered_map>

namespace delta {

class UnitScopes {
 public:
  void SetInstanceUnit(std::string_view inst_prefix, int unit);
  bool Separate() const { return !units_.empty(); }
  int UnitOf(std::string_view inst_prefix) const;
  static std::string ScopeName(int unit);
  static bool IsUnitScope(std::string_view name);

 private:
  std::unordered_map<std::string, int> units_;
};

}  // namespace delta
