#include "elaborator/cross_bin_with_covergroup.h"

namespace delta {

bool CrossIdentifierSelectIsLegal(std::string_view referenced_cross,
                                  std::string_view enclosing_cross) {
  // §19.6.1.2: a cross_identifier select_expression may name only the enclosing
  // cross; referring to any other cross is disallowed.
  return referenced_cross == enclosing_cross;
}

bool CrossMatchesCountIsLegal(int64_t evaluated_count) {
  // §19.6.1.2: the matches count shall be a positive integer.
  return evaluated_count > 0;
}

}  // namespace delta
