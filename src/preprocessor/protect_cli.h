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

  // Whether one of these options was recognized and its value refused, either
  // because the command line ended before it or because §34.5.10's three-part
  // form was not what was written. The caller carries it into its own such
  // field so the parse fails, and it is separate from TryParseProtectArg's
  // answer for the reason CliOptions::rejected_argument
  // (driver/cli_options.h) is separate from an unrecognized option: an option
  // that has already said what is wrong with its own value must not then be
  // reported as one that does not exist.
  bool rejected_argument = false;
};

// Reads one command-line argument into `opts`, answering whether it was one of
// these. `i` indexes the argument being read and is advanced past any value the
// option takes, so a caller loops over argv and consults this before its own
// options, exactly as it does for every other group.
//
// An option whose value is missing, and one whose value §34.5.10's form does
// not admit, are both answered true: the argument was this option, and what is
// wrong with it has been reported here and recorded in
// ProtectCliOptions::rejected_argument. Answering false would hand the option
// back to a caller that knows only that no parser took it, and it would report
// an option that exists as one that does not.
bool TryParseProtectArg(std::string_view arg, int& i, int argc,
                        const char* const argv[], ProtectCliOptions& opts);

}  // namespace delta
