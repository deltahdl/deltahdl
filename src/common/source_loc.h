#pragma once

#include <cstdint>
#include <string>
#include <string_view>

namespace delta {

// Where a report stands. A report about a construct carries the position of
// that construct, so somebody whose source description was rejected is told
// where it was rejected as well as what the rule is.
struct SourceLoc {
  uint32_t file_id = 0;
  uint32_t line = 0;
  uint32_t column = 0;

  bool IsValid() const { return file_id != 0 || line != 0; }

  // The report is about the run rather than about a construct written in a
  // source description, so there is no position for it to stand at. A source
  // description that cannot be read and a count of what the command line put
  // in force are reports of this kind: what they state is a fact about the
  // run. A report saying this is distinct from a caller that passed nothing,
  // which the assert-no-unlocated-diagnostics job in
  // .github/workflows/deltahdl.yml fails, and a report about a construct says
  // where the construct is instead.
  static constexpr SourceLoc None() { return SourceLoc{}; }
};

struct SourceRange {
  SourceLoc start;
  SourceLoc end;
};

// The source one line of preprocessed text was written on. §22.12 requires a
// compiler to maintain the current line number and file name of the file being
// compiled, and the preprocessor's output is not that file: it splices in the
// lines of every `include and joins a `define body that spanned continuation
// lines, so neither the name nor the count survives it. One of these per output
// line is what carries both across, so a report about a token of that line can
// name the file the user wrote and the line they wrote it on.
struct OutputLineOrigin {
  uint32_t file_id = 0;
  uint32_t line = 0;
};

}  // namespace delta
