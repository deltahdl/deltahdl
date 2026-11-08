#include "elaborator/cross_bin_with_covergroup.h"

#include <cstdint>
#include <string_view>

namespace delta {

bool CrossIdentifierSelectIsLegal(std::string_view referenced_cross,
                                  std::string_view enclosing_cross) {
  return referenced_cross == enclosing_cross;
}

bool CrossMatchesCountIsLegal(int64_t evaluated_count) {
  return evaluated_count > 0;
}

}  // namespace delta
