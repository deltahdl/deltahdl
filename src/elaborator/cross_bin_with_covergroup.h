#ifndef DELTA_ELABORATOR_CROSS_BIN_WITH_COVERGROUP_H
#define DELTA_ELABORATOR_CROSS_BIN_WITH_COVERGROUP_H

#include <cstdint>
#include <string_view>

namespace delta {

bool CrossIdentifierSelectIsLegal(std::string_view referenced_cross,
                                  std::string_view enclosing_cross);

bool CrossMatchesCountIsLegal(int64_t evaluated_count);

}  // namespace delta

#endif
