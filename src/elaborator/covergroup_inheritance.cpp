#include "elaborator/covergroup_inheritance.h"

#include <algorithm>
#include <cstdint>
#include <string>
#include <vector>

namespace delta {

bool DerivedCovergroupCanBeExtended() { return true; }

bool CovergroupReferenceResolvesToDerived(bool derived_exists,
                                          CovergroupReferenceSite site) {
  (void)site;
  return derived_exists;
}

bool BaseComponentBelongsToDerived(bool overridden_in_derived) {
  return !overridden_in_derived;
}

DerivedCoverpointRole ClassifyDerivedCoverpoint(bool name_exists_in_base) {
  return name_exists_in_base ? DerivedCoverpointRole::kOverride
                             : DerivedCoverpointRole::kAdditional;
}

std::vector<std::string> DerivedCovergroupCoverpoints(
    const std::vector<std::string>& base_names,
    const std::vector<std::string>& derived_names) {
  std::vector<std::string> result = base_names;
  for (const auto& name : derived_names) {
    if (std::find(base_names.begin(), base_names.end(), name) ==
        base_names.end()) {
      result.push_back(name);
    }
  }
  return result;
}

std::vector<std::string> DerivedCovergroupArguments(
    const std::vector<std::string>& base_arguments) {
  return base_arguments;
}

std::string DerivedCovergroupCoverageEvent(const std::string& base_event) {
  return base_event;
}

bool DerivedOptionOverridesBase(const InheritedCoverageOption& option) {
  return option.derived_specifies && option.base_specifies;
}

int32_t EffectiveDerivedOption(const InheritedCoverageOption& option) {
  if (option.derived_specifies) return option.derived_value;
  return option.base_value;
}

}  // namespace delta
