#include "simulator/foreign_code.h"

#include <array>
#include <cstdint>
#include <filesystem>
#include <string>
#include <string_view>
#include <system_error>

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

std::string_view ForeignCodeRootSwitch() { return "-sv_root"; }

void ForeignCodeLocator::SetRoot(std::string_view directory) {
  root_ = std::string(directory);
}

bool ForeignCodeLocator::HasRoot() const { return !root_.empty(); }

std::string ForeignCodeLocator::Root() const {
  if (HasRoot()) return root_;
  std::error_code ec;
  const std::filesystem::path kCwd = std::filesystem::current_path(ec);
  return ec ? std::string(".") : kCwd.string();
}

std::string ForeignCodeLocator::Resolve(std::string_view path) const {
  const std::filesystem::path kPath(path);
  if (kPath.is_absolute()) return kPath.string();
  return (std::filesystem::path(Root()) / kPath).string();
}

}  // namespace delta
