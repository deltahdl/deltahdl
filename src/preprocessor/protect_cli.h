#pragma once

#include <string>
#include <string_view>

#include "common/arg_origin.h"
#include "preprocessor/protect_keywords.h"

namespace delta {

struct ProtectCliOptions {
  const ArgOrigins* arg_origins = nullptr;
  bool encrypt = false;
  std::string exchange_key;
  ProtectKeyList keys;

  bool rejected_argument = false;
};

bool TryParseProtectArg(std::string_view arg, int& i, int argc,
                        const char* const argv[], ProtectCliOptions& opts);

}  // namespace delta
