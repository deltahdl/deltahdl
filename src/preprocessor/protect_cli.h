#pragma once

#include <string>
#include <string_view>

#include "preprocessor/protect_keywords.h"

namespace delta {

// What a caller asked of §34.3.1's encrypting mode, read off the command line.
//
// §34.3.1 gives a protected envelope two modes of processing, and the
// encrypting one reads the encryption envelopes an author wrote and leaves a
// decryption envelope in the place of each. A tool offering only the other mode
// leaves an author with no way to seal a model at all, so these are the options
// that ask for it and carry what it needs.
//
// The two key fields are the two §34.5.10 admits and are not alternatives to
// one another: `exchange_key` is the single key every region is encrypted
// under, whoever the region names, and `keys` holds the keys supplied under the
// owner and name that select them, for a text whose regions name several
// entities. They mirror PreprocConfig::protect_key and
// PreprocConfig::protect_keys, which are the same two for the decrypting mode.
struct ProtectCliOptions {
  bool encrypt = false;
  std::string exchange_key;
  ProtectKeyList keys;
};

// Reads one command-line argument into `opts`, answering whether it was one of
// these. `i` indexes the argument being read and is advanced past any value the
// option takes, so a caller loops over argv and consults this before its own
// options, exactly as it does for every other group.
//
// An option whose value is missing is not consumed, so the caller reports it as
// the unknown option it then appears to be rather than reading past the end of
// argv. That is the same answer the other option groups give, and it is what
// makes `--protect-key` with nothing after it an error rather than a key of
// nothing.
bool TryParseProtectArg(std::string_view arg, int& i, int argc,
                        const char* const argv[], ProtectCliOptions& opts);

}  // namespace delta
