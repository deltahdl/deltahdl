#pragma once

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "driver/cli_options.h"
#include "preprocessor/preprocessor.h"

namespace delta {

// The preprocessor configuration the command line asks for: its include
// directories and macro definitions, and the keys §34.3 has a reading run open
// decryption envelopes with, which an --encrypt run seals under as well.
PreprocConfig PreprocConfigFor(const CliOptions& opts);

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
