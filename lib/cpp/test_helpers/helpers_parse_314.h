#pragma once

#include "fixture_parser.h"

using namespace delta;

using ParseResult314 = ParseResult;

inline ParseResult314 Parse314(const std::string& src) {
  return ParseWithPreprocessor(src);
}

inline bool ParseOk314(const std::string& src) {
  auto result = ParseWithPreprocessor(src);
  return !result.has_errors;
}
