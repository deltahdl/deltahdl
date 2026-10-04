#include "driver/protect_license_libraries.h"

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "parser/precompiled_library.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_license.h"
#include "simulator/shared_library.h"

namespace delta {

ProtectLicenseLibraries::~ProtectLicenseLibraries() { Release(); }

ProtectLicenseAnswer ProtectLicenseLibraries::Ask(
    const ProtectLicense& license) {
  ProtectLicenseAnswer answer;
  SharedLibraryLoad load = LoadSharedLibrary(license.library);
  if (load.handle == nullptr) {
    answer.why_not_called = load.error;
    return answer;
  }
  if (license.has_exit) {
    void* exit_symbol = SharedLibrarySymbol(load.handle, license.exit);
    if (exit_symbol != nullptr) {
      exits_.push_back(reinterpret_cast<void (*)()>(exit_symbol));
    }
  }
  void* entry_symbol = SharedLibrarySymbol(load.handle, license.entry);
  if (entry_symbol == nullptr) {
    answer.why_not_called = "the library defines no function of that name";
    return answer;
  }
  auto* entry = reinterpret_cast<int (*)(const char*)>(entry_symbol);
  answer.called = true;
  answer.returned = static_cast<int64_t>(entry(license.feature.c_str()));
  return answer;
}

ProtectLicenseAsk ProtectLicenseLibraries::Asker() {
  return [this](const ProtectLicense& license) { return Ask(license); };
}

void ProtectLicenseLibraries::Release() {
  std::vector<void (*)()> exits;
  exits.swap(exits_);
  for (void (*exit_function)() : exits) exit_function();
}

bool RuntimeLicensesGranted(const std::vector<ProtectRuntimeLicense>& licenses,
                            ProtectLicenseLibraries& libraries,
                            DiagEngine& diag) {
  bool granted = true;
  for (const ProtectRuntimeLicense& use : licenses) {
    ProtectLicenseAnswer answer = libraries.Ask(use.license);
    if (ProtectLicenseGranted(use.license, answer)) continue;
    diag.Error(
        use.loc,
        ProtectLicenseRefusal(kRuntimeLicenseKeyword, use.license, answer),
        Subclause("34.5.29.2"));
    granted = false;
  }
  return granted;
}

bool PrecompiledRuntimeLicensesGranted(
    const std::vector<std::string>& library_paths,
    ProtectLicenseLibraries& libraries, DiagEngine& diag) {
  std::vector<ProtectRuntimeLicense> licenses;
  for (const std::string& path : library_paths) {
    for (ProtectLicense& license : PrecompiledLibrary::RuntimeLicenses(path)) {
      licenses.push_back({std::move(license), SourceLoc::None()});
    }
  }
  return RuntimeLicensesGranted(licenses, libraries, diag);
}

}  // namespace delta
