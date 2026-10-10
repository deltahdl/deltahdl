#pragma once

#include <string>
#include <string_view>
#include <unordered_map>

namespace delta {

// §3.12.1 (printed page 56): in a design of several compilation units, the unit
// each instance's module was declared in, whose compilation-unit-scope
// declarations the instance's names reach. A unit's declarations stand under
// the scope name "$unit#k" for unit k, where a design of one unit keeps
// "$unit". Holds nothing for a design of one unit.
class UnitScopes {
 public:
  // Records that the instance `inst_prefix` names, "" for the first top, was
  // declared in unit `unit`; nothing for a negative unit, a module of a design
  // of one unit.
  void SetInstanceUnit(std::string_view inst_prefix, int unit);
  // Whether the design is of several units.
  bool Separate() const { return !units_.empty(); }
  // The unit of the instance a name written under `inst_prefix` stands in: the
  // nearest recorded instance holding it, a generate block's names extending
  // its instance's prefix. -1 where none is recorded.
  int UnitOf(std::string_view inst_prefix) const;
  // The scope name unit `unit`'s declarations stand under: "$unit#k", or
  // "$unit" for a negative unit.
  static std::string ScopeName(int unit);
  // Whether `name` is a compilation unit's scope name.
  static bool IsUnitScope(std::string_view name);

 private:
  std::unordered_map<std::string, int> units_;
};

}  // namespace delta
