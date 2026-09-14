#include "simulator/foreign_code.h"

namespace delta {

ForeignCodeRedistributionForm ForeignCodeIntendedRedistributionForm() {
  return ForeignCodeRedistributionForm::kSharedObject;
}

bool ForeignCodeGuidelinesAreCommonToApplications() { return true; }

}  // namespace delta
