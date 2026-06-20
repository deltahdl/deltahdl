#include "elaborator/covergroup_inheritance.h"

#include <algorithm>

namespace delta {

bool DerivedCovergroupCanBeExtended() {
  // §19.4.1: a derived covergroup may act as the base covergroup for
  // inheritance in another class, so it can always be extended further.
  return true;
}

bool CovergroupReferenceResolvesToDerived(bool derived_exists,
                                          CovergroupReferenceSite site) {
  // §19.4.1: a derived covergroup replaces the instance of the base covergroup,
  // so every reference to the shared name — whether written in the deriving
  // class or in any of its base classes — resolves to the derived instance.
  (void)site;
  return derived_exists;
}

bool BaseComponentBelongsToDerived(bool overridden_in_derived) {
  // §19.4.1: unless it is overridden, a base covergroup component is considered
  // to also belong to the derived covergroup.
  return !overridden_in_derived;
}

DerivedCoverpointRole ClassifyDerivedCoverpoint(bool name_exists_in_base) {
  // §19.4.1: a new coverpoint name is an additional coverpoint; a name shared
  // with the base covergroup overrides the base coverpoint of that name.
  return name_exists_in_base ? DerivedCoverpointRole::kOverride
                             : DerivedCoverpointRole::kAdditional;
}

std::vector<std::string> DerivedCovergroupCoverpoints(
    const std::vector<std::string>& base_names,
    const std::vector<std::string>& derived_names) {
  // §19.4.1: inherit every base coverpoint (each still belongs to the derived
  // covergroup; a same-named derived coverpoint merely replaces it in place),
  // then append the derived coverpoints whose names are new to the base.
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
  // §19.4.1: the derived covergroup implicitly has the same argument list as
  // the base covergroup.
  return base_arguments;
}

std::string DerivedCovergroupCoverageEvent(const std::string& base_event) {
  // §19.4.1: the derived covergroup shall use the base covergroup's coverage
  // event.
  return base_event;
}

bool DerivedOptionOverridesBase(const InheritedCoverageOption& option) {
  // §19.4.1: an option specified in the derived covergroup that is also
  // specified in the base covergroup overrides the base value.
  return option.derived_specifies && option.base_specifies;
}

int32_t EffectiveDerivedOption(const InheritedCoverageOption& option) {
  // §19.4.1: a value specified in the derived covergroup overrides the base;
  // otherwise a base value that the derived does not specify still applies.
  if (option.derived_specifies) return option.derived_value;
  return option.base_value;
}

}  // namespace delta
