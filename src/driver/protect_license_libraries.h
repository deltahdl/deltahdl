#pragma once

#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_license.h"

namespace delta {

class ProtectLicenseLibraries {
 public:
  ProtectLicenseLibraries() = default;
  ProtectLicenseLibraries(const ProtectLicenseLibraries&) = delete;
  ProtectLicenseLibraries& operator=(const ProtectLicenseLibraries&) = delete;
  ProtectLicenseLibraries(ProtectLicenseLibraries&&) = delete;
  ProtectLicenseLibraries& operator=(ProtectLicenseLibraries&&) = delete;
  ~ProtectLicenseLibraries();

  ProtectLicenseAnswer Ask(const ProtectLicense& license);

  ProtectLicenseAsk Asker();

  void Release();

 private:
  std::vector<void (*)()> exits_;
};

bool RuntimeLicensesGranted(const std::vector<ProtectRuntimeLicense>& licenses,
                            ProtectLicenseLibraries& libraries,
                            DiagEngine& diag);

bool PrecompiledRuntimeLicensesGranted(
    const std::vector<std::string>& library_paths,
    ProtectLicenseLibraries& libraries, DiagEngine& diag);

}  // namespace delta
