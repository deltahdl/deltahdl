#pragma once

#include <string_view>

namespace delta {

inline bool ArrayMethodWritesItsArray(std::string_view method) {
  return method == "delete" || method == "insert" || method == "push_back" ||
         method == "push_front" || method == "pop_back" ||
         method == "pop_front" || method == "sort" || method == "rsort" ||
         method == "reverse" || method == "shuffle";
}

inline bool ArrayMethodWritesItsIndex(std::string_view method) {
  return method == "first" || method == "last" || method == "next" ||
         method == "prev";
}

}  // namespace delta
