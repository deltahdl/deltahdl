#ifndef DELTA_SIMULATOR_FOREIGN_CODE_H_
#define DELTA_SIMULATOR_FOREIGN_CODE_H_

#include <array>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"

namespace delta {

enum class ForeignCodeRedistributionForm : uint8_t {
  kSharedObject,
  kSourceCode,
  kStaticArchiveOnly,
};

ForeignCodeRedistributionForm ForeignCodeIntendedRedistributionForm();

bool ForeignCodeGuidelinesAreCommonToApplications();

enum class ForeignCodeInterface : uint8_t { kDpi, kVpi };

bool ForeignCodeAnnexApplies(ForeignCodeInterface included_through);
bool ForeignCodeIsLimitedToCOrCpp();

enum class ForeignCodeForm : uint8_t { kObjectCode, kSourceCode };

ForeignCodeForm ForeignCodeProvidedForm();
bool ForeignCodeObjectFormMustBeSupported();

enum class ForeignCodeFacility : uint8_t {
  kSpecifyLocationOfFiles,
  kSpecifyFilesToLoad,
  kProvideObjectCode,
};

std::array<ForeignCodeFacility, 3> ForeignCodeFacilitiesDefined();

enum class ForeignCodeObjectPackaging : uint8_t { kSharedLibrary, kArchive };

bool ForeignCodeObjectMayBePackagedAs(ForeignCodeObjectPackaging packaging);

enum class ForeignCodeInclusionMethod : uint8_t {
  kBootstrapFile,
  kToolSwitches
};

enum class ForeignCodeUseCase : uint8_t { kVendorIp, kProjectTeam, kUser };

uint32_t ForeignCodeImplementationsUsuallyRequired();
ForeignCodeInclusionMethod ForeignCodeMethodOftenCovering(
    ForeignCodeUseCase use_case);
bool ForeignCodeUseCaseMayUseBootstrapFile(ForeignCodeUseCase use_case);
bool ForeignCodeSwitchNamesAreRequirements();

std::string_view ForeignCodeRootSwitch();

class ForeignCodeLocator {
 public:
  void SetRoot(std::string_view directory);
  bool HasRoot() const;
  std::string Root() const;
  std::string Resolve(std::string_view path) const;

 private:
  std::string root_;
};

std::string_view ForeignCodeBootstrapHeader();

struct ForeignCodeBootstrap {
  std::vector<std::string> libraries;
  std::string error;
  bool Ok() const { return error.empty(); }
};

ForeignCodeBootstrap ParseForeignCodeBootstrap(std::string_view text);

enum class ForeignCodeSpecificationMethod : uint8_t {
  kBootstrapFileEntry,
  kLibSwitch,
};

std::string_view ForeignCodeLibListSwitch();
std::string_view ForeignCodeLibSwitch();
std::string_view ForeignCodeSwitchOf(ForeignCodeSpecificationMethod method);
bool ForeignCodeSwitchMayRepeat(std::string_view switch_name);
bool ForeignCodeMethodsAreAvailableConcurrently();
bool ForeignCodeMethodsMayBeMixed();

std::string_view ForeignCodeSharedLibraryExtension();
std::string ForeignCodeSharedLibraryFileName(
    std::string_view pathname_without_extension);

enum class ForeignCodeParty : uint8_t { kProvider, kApplication };

enum class ForeignCodeDuty : uint8_t {
  kIdentifyTheExtension,
  kAppendTheExtension,
  kResolveExternalReferences,
  kAvoidInterferenceWithOtherSoftware,
  kSelectTheSoftwareVersion,
};

ForeignCodeParty ForeignCodeResponsibleFor(ForeignCodeDuty duty);

enum class ForeignCodeLoadScope : uint8_t {
  kReferencedObjectCodeOnly,
  kEveryFunctionOfTheLibrary,
};

ForeignCodeLoadScope ForeignCodeLoadRequired();

struct ForeignCodeLibrary {
  std::string path;
  ForeignCodeSpecificationMethod method =
      ForeignCodeSpecificationMethod::kBootstrapFileEntry;
};

bool ForeignCodeIsSameFile(std::string_view a, std::string_view b);

std::vector<ForeignCodeLibrary> ForeignCodeLoadOrder(
    const std::vector<std::string>& bootstrap_entries,
    const std::vector<std::string>& lib_switch_values);

struct ForeignCodeLibList {
  std::string path;
  std::string root;
};

std::vector<std::string> ForeignCodeResolveBootstrapEntries(
    const ForeignCodeBootstrap& file, std::string_view root);

std::vector<std::string> ForeignCodeLibraryFileNames(
    const std::vector<ForeignCodeLibrary>& order);

bool ForeignCodeLoadLibraries(const std::vector<std::string>& bootstrap_entries,
                              const std::vector<std::string>& lib_switch_values,
                              DiagEngine& diag);

}  // namespace delta

#endif
