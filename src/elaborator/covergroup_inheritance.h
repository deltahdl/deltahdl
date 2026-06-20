#ifndef DELTA_ELABORATOR_COVERGROUP_INHERITANCE_H
#define DELTA_ELABORATOR_COVERGROUP_INHERITANCE_H

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

namespace delta {

// §19.4.1 governs embedded covergroup inheritance: the `covergroup extends
// base ;` form that defines a derived covergroup reusing the base covergroup's
// name. The legality of the extends declaration (the base must be defined in a
// base class) is enforced directly in the class validator; the helpers here
// model the remaining structural rules the text of §19.4.1 adds — what a
// derived covergroup inherits, what it may override, and how its components,
// arguments, and coverage event are composed from the base. The covergroup
// construct itself belongs to §19.3, and how the inherited components feed the
// coverage computation belongs to the simulator (see §19.4.1 helpers in
// coverage.h).

// §19.4.1: a derived covergroup in one class may itself act as the base
// covergroup for covergroup inheritance in another class, so the inheritance
// chain has no fixed depth. A derived covergroup is therefore always eligible
// to be extended again.
bool DerivedCovergroupCanBeExtended();

// §19.4.1: the side of an inheritance relationship from which a covergroup name
// is referenced. When a derived covergroup extends a base, it replaces the base
// instance with a derived instance, so references resolve to the derived
// instance both within the class that derives it and within all of that class's
// base classes.
enum class CovergroupReferenceSite : uint8_t {
  // A reference written in a base class that declared the base covergroup.
  kBaseClass,
  // A reference written in the derived class.
  kDerivedClass,
};

// §19.4.1: once a derived covergroup exists, every reference to the shared name
// resolves to the derived instance, regardless of whether the reference appears
// in the deriving class or in one of its base classes. Returns true when the
// reference resolves to the derived instance.
bool CovergroupReferenceResolvesToDerived(bool derived_exists,
                                          CovergroupReferenceSite site);

// §19.4.1: unless the derived covergroup overrides a base component (as
// described for coverpoints, crosses, and options), every component belonging
// to the base covergroup is considered to also belong to the derived
// covergroup. Returns true when the base component is inherited by the derived
// covergroup.
bool BaseComponentBelongsToDerived(bool overridden_in_derived);

// §19.4.1: the role a coverpoint declared in the derived covergroup plays
// relative to the base covergroup.
enum class DerivedCoverpointRole : uint8_t {
  // The name does not occur in the base covergroup, so the derived coverpoint
  // is
  // an additional coverage point that is sampled alongside the inherited ones.
  kAdditional,
  // The name matches a base coverpoint, so the derived coverpoint replaces
  // (overrides) the base coverpoint of the same name.
  kOverride,
};

// §19.4.1: a derived coverpoint whose name is new to the base covergroup is an
// additional coverpoint; a derived coverpoint whose name is identical to a base
// coverpoint overrides it.
DerivedCoverpointRole ClassifyDerivedCoverpoint(bool name_exists_in_base);

// §19.4.1: the coverpoint names belonging to a derived covergroup. Every base
// coverpoint is inherited unless the derived covergroup defines a coverpoint of
// the same name (which replaces it rather than adding a second), and every
// derived coverpoint with a name new to the base is appended as an additional
// coverpoint. Base order is preserved, with new derived coverpoints following.
std::vector<std::string> DerivedCovergroupCoverpoints(
    const std::vector<std::string>& base_names,
    const std::vector<std::string>& derived_names);

// §19.4.1: the argument list of a derived covergroup. The extends form supplies
// no argument list of its own, so when the base covergroup has a list of
// arguments the derived covergroup implicitly has that same list.
std::vector<std::string> DerivedCovergroupArguments(
    const std::vector<std::string>& base_arguments);

// §19.4.1: the coverage event of a derived covergroup. The extends form
// specifies no coverage event of its own; when the base covergroup specifies a
// coverage event the derived covergroup shall use that same event.
std::string DerivedCovergroupCoverageEvent(const std::string& base_event);

// §19.4.1: a coverage option as seen across an inheritance pair. A value may be
// specified at the base, at the derived covergroup, or at both.
struct InheritedCoverageOption {
  bool base_specifies = false;
  int32_t base_value = 0;
  bool derived_specifies = false;
  int32_t derived_value = 0;
};

// §19.4.1: a coverage option specified in the derived covergroup that is also
// specified in the base covergroup overrides the base value. Returns true when
// the derived covergroup overrides the base option.
bool DerivedOptionOverridesBase(const InheritedCoverageOption& option);

// §19.4.1: the effective value of a coverage option for a derived covergroup. A
// value specified in the derived covergroup overrides the base; a base value
// the derived covergroup does not specify still applies to the derived
// covergroup.
int32_t EffectiveDerivedOption(const InheritedCoverageOption& option);

}  // namespace delta

#endif  // DELTA_ELABORATOR_COVERGROUP_INHERITANCE_H
