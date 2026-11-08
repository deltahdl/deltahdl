#pragma once

#include <string_view>

namespace delta {

inline bool StringMethodWritesItsObject(std::string_view method) {
  return method == "putc" || method == "itoa" || method == "hextoa" ||
         method == "octtoa" || method == "bintoa" || method == "realtoa";
}

inline bool StringMethodAnswersAValue(std::string_view method) {
  return method == "len" || method == "getc" || method == "toupper" ||
         method == "tolower" || method == "compare" || method == "icompare" ||
         method == "substr" || method == "atoi" || method == "atohex" ||
         method == "atooct" || method == "atobin" || method == "atoreal";
}

}  // namespace delta
