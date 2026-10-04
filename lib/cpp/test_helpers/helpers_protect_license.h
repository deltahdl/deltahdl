#pragma once

#include <cstdint>

#include "preprocessor/protect_license.h"

using namespace delta;

// The answer of a reading that holds every licence it is asked about: the
// entry function is called and returns the match value, so §34.5.28.2 lets
// the model be decrypted. A test whose subject is what an envelope carries
// rather than whether its licence is held reads it this way.
inline ProtectLicenseAsk GrantingEveryLicence() {
  return [](const ProtectLicense& license) {
    ProtectLicenseAnswer answer;
    answer.called = true;
    answer.returned = static_cast<int64_t>(license.match);
    return answer;
  };
}
