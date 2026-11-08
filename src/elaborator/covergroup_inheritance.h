#ifndef DELTA_ELABORATOR_COVERGROUP_INHERITANCE_H
#define DELTA_ELABORATOR_COVERGROUP_INHERITANCE_H

#include <cstdint>
#include <string>
#include <vector>

namespace delta {

bool DerivedCovergroupCanBeExtended();

enum class CovergroupReferenceSite : uint8_t {
  kBaseClass,
  kDerivedClass,
};

bool CovergroupReferenceResolvesToDerived(bool derived_exists,
                                          CovergroupReferenceSite site);

bool BaseComponentBelongsToDerived(bool overridden_in_derived);

enum class DerivedCoverpointRole : uint8_t {
  kAdditional,
  kOverride,
};

DerivedCoverpointRole ClassifyDerivedCoverpoint(bool name_exists_in_base);

std::vector<std::string> DerivedCovergroupCoverpoints(
    const std::vector<std::string>& base_names,
    const std::vector<std::string>& derived_names);

std::vector<std::string> DerivedCovergroupArguments(
    const std::vector<std::string>& base_arguments);

std::string DerivedCovergroupCoverageEvent(const std::string& base_event);

struct InheritedCoverageOption {
  bool base_specifies = false;
  int32_t base_value = 0;
  bool derived_specifies = false;
  int32_t derived_value = 0;
};

bool DerivedOptionOverridesBase(const InheritedCoverageOption& option);

int32_t EffectiveDerivedOption(const InheritedCoverageOption& option);

}  // namespace delta

#endif
