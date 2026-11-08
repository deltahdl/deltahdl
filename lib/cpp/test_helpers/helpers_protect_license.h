#pragma once

#include <cstdint>

#include "preprocessor/protect_license.h"

using namespace delta;

inline ProtectLicenseAsk GrantingEveryLicence() {
  return [](const ProtectLicense& license) {
    ProtectLicenseAnswer answer;
    answer.called = true;
    answer.returned = static_cast<int64_t>(license.match);
    return answer;
  };
}
