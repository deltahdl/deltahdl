#pragma once

// The lexer and the few readers the SDF parser's translation units share:
// src/simulator/sdf_parser.cpp reads a file's header, its cells and their
// DELAY and LABEL sections, and src/simulator/sdf_parser_timing_check.cpp the
// entries of a TIMINGCHECK section (§32.4.2), each through the tokens these
// produce. Nothing outside the two includes it.

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/sdf_parser.h"

namespace delta {

enum class SdfTokKind : uint8_t {
  kLParen,
  kRParen,
  kColon,
  kIdent,
  kString,
  kNumber,
  kEof,
};

struct SdfToken {
  SdfTokKind kind = SdfTokKind::kEof;
  std::string_view text;
  uint64_t num_val = 0;
  // §32.7: `num_val` is the magnitude alone, so a number written with a
  // leading minus sign is told apart from the same number written without one.
  bool is_negative = false;
  // The magnitude exactly as written, a fraction or an exponent included;
  // `num_val` is it rounded to a whole number.
  double real_val = 0.0;
};

void SkipWhitespace(std::string_view& s);
SdfToken NextSdfToken(std::string_view& s);
bool Expect(std::string_view& s, SdfTokKind kind);
SdfDelayValue ParseDelayVal(std::string_view& s);

// §32.4.1: the tokens of a COND condition expression, up to the `(` or `)`
// that ends it, and those tokens joined back into its text.
std::vector<std::string> ParseSdfCondTokens(std::string_view& s);
std::string JoinSdfCondTokens(const std::vector<std::string>& tokens,
                              std::size_t count);

// §32.4.2 Table 32-2: the check a TIMINGCHECK entry keyword annotates, false
// for a keyword the annotator does not recognize; and one entry of that type,
// its keyword already read, through its closing `)`.
bool MapCheckType(std::string_view name, SdfCheckType& out);
SdfTimingCheck ParseOneTc(std::string_view& s, SdfCheckType type);

}  // namespace delta
