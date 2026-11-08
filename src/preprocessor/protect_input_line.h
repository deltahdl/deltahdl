#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"

namespace delta {

std::vector<std::string_view> SplitLines(std::string_view text);

SourceLoc LineOf(uint32_t file_id, uint32_t line);

enum class EnvelopeDelimiter : uint8_t { kNone, kBegin, kEnd };

struct DelimiterMatch {
  EnvelopeDelimiter kind;
  std::string_view keyword;
};

DelimiterMatch DelimiterOfLine(std::string_view line);

bool BlockCommentOpenAfter(std::string_view line, bool open_at_start);

std::string OpeningDirectiveOf(std::string_view line,
                               const DelimiterMatch& delimiter,
                               std::string_view replacement);

std::string ClosingDirectiveOf(std::string_view line,
                               const DelimiterMatch& delimiter,
                               std::string_view replacement);

std::string ExpressionsAheadOfDelimiter(std::string_view line,
                                        const DelimiterMatch& delimiter);

std::string ExpressionsBehindDelimiter(std::string_view line,
                                       const DelimiterMatch& delimiter);

class PreviouslyProtectedBlock {
 public:
  bool Contains(std::string_view line);

 private:
  size_t depth_ = 0;
};

struct InputLine {
  bool previously_protected;
  DelimiterMatch delimiter;
};

void ReportNestedRegion(const DelimiterMatch& delimiter, DiagEngine* diag,
                        SourceLoc loc);

InputLine ReadInputLine(std::string_view line, PreviouslyProtectedBlock* block,
                        DiagEngine* diag, SourceLoc loc);

}  // namespace delta
