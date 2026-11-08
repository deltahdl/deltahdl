#pragma once

#include <string>

inline bool IsGatePrimitiveWord(const std::string& word) {
  return word == "and" || word == "nand" || word == "nor" || word == "or" ||
         word == "xnor" || word == "xor";
}

inline bool IsAggregateOpenerWord(const std::string& word) {
  return word == "struct" || word == "union";
}
