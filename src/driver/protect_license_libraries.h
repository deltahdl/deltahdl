#pragma once

#include <vector>

#include "common/diagnostic.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_license.h"

namespace delta {

// The libraries §34.5.28.2 and §34.5.29.2 have a tool load to ask a protected
// model's licences, and the exit functions those licences name. Each
// subclause has a named exit function called before the tool exits, so that
// the licence can be released; this object calls them when it is released or
// destroyed, and the run holds it until it ends.
//
// The standard gives the two functions no C signature. The entry function is
// called as `int entry(const char* feature)`, being passed the feature string
// and returning the value compared with the match value, and the exit function
// as `void exit(void)`, being passed and returning nothing either subclause
// names.
class ProtectLicenseLibraries {
 public:
  ProtectLicenseLibraries() = default;
  ProtectLicenseLibraries(const ProtectLicenseLibraries&) = delete;
  ProtectLicenseLibraries& operator=(const ProtectLicenseLibraries&) = delete;
  ProtectLicenseLibraries(ProtectLicenseLibraries&&) = delete;
  ProtectLicenseLibraries& operator=(ProtectLicenseLibraries&&) = delete;
  ~ProtectLicenseLibraries();

  // Loads the library `license` names, calls its entry function with the
  // feature string, and answers what it returned, or why it could not be
  // called. The exit function the licence names is kept for Release, whether
  // or not the answer licenses the tool, since either way the tool goes on to
  // exit.
  ProtectLicenseAnswer Ask(const ProtectLicense& license);

  // Ask, as the callback a preprocessor configuration is given. The callback
  // refers to this object, which outlives the reading it is handed to.
  ProtectLicenseAsk Asker();

  // Calls each exit function kept so far, once, in the order the licences
  // naming them were asked.
  void Release();

 private:
  std::vector<void (*)()> exits_;
};

// §34.5.29.2: asks each of `licenses` through `libraries`, before the model is
// executed, and reports each that does not license the tool at the place it
// was met. Answers whether all of them do, which is whether execution may
// begin.
bool RuntimeLicensesGranted(const std::vector<ProtectRuntimeLicense>& licenses,
                            ProtectLicenseLibraries& libraries,
                            DiagEngine& diag);

}  // namespace delta
