#include "preprocessor/protect_input_line.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_key_block.h"
#include "preprocessor/protect_pragma_line.h"
#include "preprocessor/protect_processing.h"

namespace delta {
namespace {

// The expressions a delimiter is followed by on its own line: `rest` up to any
// comment written there, and without the whitespace that ran up to it.
//
// Neither a comment nor the space ahead of it is a pragma expression, and
// neither states anything about the envelope, so neither is among the things an
// encrypting tool carries. Leaving the comment behind is also what keeps the
// envelope readable: a block comment the author never closed would otherwise be
// carried onto the produced directive and take the expressions written after it
// -- the description of the encryption, and the block itself -- into the
// comment with it.
std::string_view ExpressionsAfterDelimiter(std::string_view rest) {
  size_t end = rest.size();
  size_t i = 0;
  while (i < rest.size()) {
    // A comment opener inside a string value is content of that value.
    if (rest[i] == '"') {
      i = SkipStringValue(rest, i);
    } else if (StartsLineComment(rest, i) || rest.compare(i, 2, "/*") == 0) {
      end = i;
      break;
    } else {
      ++i;
    }
  }
  return TrimTrailing(rest.substr(0, end));
}

}  // namespace

std::vector<std::string_view> SplitLines(std::string_view text) {
  std::vector<std::string_view> lines;
  size_t pos = 0;
  while (pos < text.size()) {
    size_t eol = text.find('\n', pos);
    size_t end = eol == std::string_view::npos ? text.size() : eol + 1;
    lines.push_back(text.substr(pos, end - pos));
    pos = end;
  }
  return lines;
}

SourceLoc LineOf(uint32_t file_id, uint32_t line) {
  return SourceLoc{file_id, line, 1};
}

DelimiterMatch DelimiterOfLine(std::string_view line) {
  std::string_view body;
  if (!ProtectPragmaLine(line, &body)) return {EnvelopeDelimiter::kNone, {}};
  for (const ListedKeyword& keyword : TopLevelKeywords(body)) {
    if (OpensEncryptionEnvelope(keyword.name, keyword.has_value)) {
      return {EnvelopeDelimiter::kBegin, keyword.name};
    }
    if (ClosesEncryptionEnvelope(keyword.name, keyword.has_value)) {
      return {EnvelopeDelimiter::kEnd, keyword.name};
    }
  }
  return {EnvelopeDelimiter::kNone, {}};
}

std::string TransformedDelimiterLine(std::string_view line,
                                     const DelimiterMatch& delimiter,
                                     std::string_view replacement) {
  auto at = static_cast<size_t>(delimiter.keyword.data() - line.data());
  std::string transformed(line.substr(0, at));
  transformed.append(replacement);
  transformed.append(
      ExpressionsAfterDelimiter(line.substr(at + delimiter.keyword.size())));
  // The last line of a source text need not be terminated, and a trimmed
  // comment takes the terminator with it. What follows this line either way is
  // a directive of its own.
  if (transformed.back() != '\n') transformed.push_back('\n');
  return transformed;
}

bool PreviouslyProtectedBlock::Contains(std::string_view line) {
  if (NamesBareKeyword(line, kBeginDecryptionKeyword)) {
    ++depth_;
    return true;
  }
  if (depth_ > 0 && NamesBareKeyword(line, kEndDecryptionKeyword)) {
    --depth_;
    return true;
  }
  return depth_ > 0;
}

void ReportNestedRegion(const DelimiterMatch& delimiter, DiagEngine* diag,
                        SourceLoc loc) {
  if (diag != nullptr && delimiter.kind == EnvelopeDelimiter::kBegin) {
    diag->Error(loc,
                "protect pragma begin expression opens a region inside a "
                "begin-end block that is still open",
                Subclause("34.5.1"));
  }
}

InputLine ReadInputLine(std::string_view line, PreviouslyProtectedBlock* block,
                        DiagEngine* diag, SourceLoc loc) {
  if (block->Contains(line)) {
    return {true, {EnvelopeDelimiter::kNone, {}}};
  }
  // §34.5.15 makes a data block found in an input file an error unless a
  // previously generated protected block contains it. This line is outside
  // every one of them, so a block written here is the block of no envelope --
  // there is nothing for it to have come out of, and nothing that could read
  // it back. The line is still carried across like any other; what the
  // condition costs is a report rather than the transformation.
  if (diag != nullptr && NamesKeyword(line, kDataBlockKeyword)) {
    diag->Error(loc,
                "protect pragma data_block is written where no previously "
                "generated begin_protected-end_protected block contains it",
                Subclause("34.5.15"));
  }
  // §34.5.27 states the same of a key block, and it costs the same: outside
  // every previously generated protected block there is no envelope whose keys
  // a key block here could be carrying, and no key it could have been encrypted
  // under either.
  if (diag != nullptr && NamesKeyword(line, kKeyBlockKeyword)) {
    diag->Error(loc,
                "protect pragma key_block is written where no previously "
                "generated begin_protected-end_protected block contains it",
                Subclause("34.5.27"));
  }
  return {false, DelimiterOfLine(line)};
}

}  // namespace delta
