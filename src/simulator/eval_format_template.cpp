#include <cctype>
#include <cstddef>
#include <string>
#include <string_view>

#include "parser/ast_expr.h"
#include "simulator/evaluation.h"

namespace delta {

std::string ExtractFormatString(const Expr* first_arg) {
  return std::string(StringLiteralBody(first_arg->text));
}

static size_t SkipFieldWidthAndPrecision(std::string_view fmt, size_t j) {
  while (j < fmt.size() && std::isdigit(static_cast<unsigned char>(fmt[j])))
    ++j;
  if (j < fmt.size() && fmt[j] == '.') {
    ++j;
    while (j < fmt.size() && std::isdigit(static_cast<unsigned char>(fmt[j])))
      ++j;
  }
  return j;
}

size_t CountFormatConversions(std::string_view fmt) {
  size_t count = 0;
  for (size_t i = 0; i + 1 < fmt.size(); ++i) {
    if (fmt[i] == '\\') {
      ++i;
      continue;
    }
    if (fmt[i] != '%') continue;
    size_t j = i + 1;
    if (fmt[j] == '%') {
      i = j;
      continue;
    }
    j = SkipFieldWidthAndPrecision(fmt, j);
    char spec = j < fmt.size() ? static_cast<char>(std::tolower(
                                     static_cast<unsigned char>(fmt[j])))
                               : 'd';
    if (spec != 'm' && spec != 'l') ++count;
    i = j;
  }
  return count;
}

}  // namespace delta
