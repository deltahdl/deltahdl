#pragma once

#include <optional>
#include <string_view>

#include "lexer/token.h"

namespace delta {

std::optional<TokenKind> lookup_keyword(std::string_view text);

}  // namespace delta
