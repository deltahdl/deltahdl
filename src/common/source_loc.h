#pragma once

#include <cstdint>
#include <string>
#include <string_view>

namespace delta {

struct SourceLoc {
    uint32_t file_id = 0;
    uint32_t line = 0;
    uint32_t column = 0;

    bool is_valid() const { return file_id != 0 || line != 0; }
};

struct SourceRange {
    SourceLoc start;
    SourceLoc end;
};

} // namespace delta
