#pragma once

#include <cstdint>

namespace delta {

struct SourceLoc {
  uint32_t file_id = 0;
  uint32_t line = 0;
  uint32_t column = 0;

  bool IsValid() const { return file_id != 0 || line != 0; }

  static constexpr SourceLoc None() { return SourceLoc{}; }
};

struct SourceRange {
  SourceLoc start;
  SourceLoc end;
};

struct OutputLineOrigin {
  uint32_t file_id = 0;
  uint32_t line = 0;
};

}  // namespace delta
