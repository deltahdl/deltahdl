#include "simulator/foreign_code.h"

#include <array>
#include <cstdint>

namespace delta {

ForeignCodeRedistributionForm ForeignCodeIntendedRedistributionForm() {
  return ForeignCodeRedistributionForm::kSharedObject;
}

bool ForeignCodeGuidelinesAreCommonToApplications() { return true; }

bool ForeignCodeAnnexApplies(ForeignCodeInterface included_through) {
  return included_through == ForeignCodeInterface::kDpi;
}

bool ForeignCodeIsLimitedToCOrCpp() { return false; }

ForeignCodeForm ForeignCodeProvidedForm() {
  return ForeignCodeForm::kObjectCode;
}

bool ForeignCodeObjectFormMustBeSupported() { return true; }

std::array<ForeignCodeFacility, 3> ForeignCodeFacilitiesDefined() {
  return {ForeignCodeFacility::kSpecifyLocationOfFiles,
          ForeignCodeFacility::kSpecifyFilesToLoad,
          ForeignCodeFacility::kProvideObjectCode};
}

bool ForeignCodeObjectMayBePackagedAs(
    ForeignCodeObjectPackaging /*packaging*/) {
  return true;
}

uint32_t ForeignCodeImplementationsUsuallyRequired() { return 2; }

ForeignCodeInclusionMethod ForeignCodeMethodOftenCovering(
    ForeignCodeUseCase use_case) {
  return use_case == ForeignCodeUseCase::kVendorIp
             ? ForeignCodeInclusionMethod::kBootstrapFile
             : ForeignCodeInclusionMethod::kToolSwitches;
}

bool ForeignCodeUseCaseMayUseBootstrapFile(ForeignCodeUseCase /*use_case*/) {
  return true;
}

bool ForeignCodeSwitchNamesAreRequirements() { return false; }

}  // namespace delta
