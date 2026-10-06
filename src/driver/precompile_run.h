#pragma once

#include <optional>
#include <string>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "driver/cli_options.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_license.h"

namespace delta {

// The preprocessor configuration the command line asks for: its include
// directories and macro definitions, and the keys §34.3 has a reading run open
// decryption envelopes with, which an --encrypt run seals under as well. A
// decrypt_license met in an encrypted model is asked through `ask_license`
// (§34.5.28.2).
PreprocConfig PreprocConfigFor(const CliOptions& opts,
                               ProtectLicenseAsk ask_license);

// The text of the source file at `path`, or nothing where it cannot be opened,
// which is reported. An empty file answers empty text, which A.1.2 makes valid
// source text: source_text is an optional timeunits_declaration followed by any
// number of descriptions, none at all among them. Every run mode that reads the
// command line's source files reads them through this.
std::optional<std::string> ReadSource(const std::string& path);

// §33.5.3's separate compilation tool: the invocation that compiles source
// descriptions into a library rather than binding a design. "It is essential
// that library cells persist, and the compiled forms shall, therefore, exist
// somewhere in the filesystem", which is what --precompile-out names and what a
// later --load-lib reads.
//
// Each source is preprocessed as an ordinary compile preprocesses it and
// parsed once, its errors reported at its own file and line through `diag`;
// what is written is the preprocessed text with the directive state the
// preprocessor recorded for it (PrecompiledDirectives). Answers the
// invocation's exit status.
int RunPrecompile(const CliOptions& opts, SourceManager& src_mgr,
                  DiagEngine& diag);

}  // namespace delta
