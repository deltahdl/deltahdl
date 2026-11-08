#pragma once

#include <optional>
#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "driver/cli_options.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_license.h"

namespace delta {

PreprocConfig PreprocConfigFor(const CliOptions& opts,
                               ProtectLicenseAsk ask_license);

std::optional<std::string> ReadSource(const std::string& path);

int RunPrecompile(const CliOptions& opts, SourceManager& src_mgr,
                  DiagEngine& diag);

}  // namespace delta
