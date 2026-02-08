#pragma once

#include "lexer/token.h"

#include <optional>
#include <string_view>

namespace delta {

std::optional<TokenKind> lookup_keyword(std::string_view text);

} // namespace delta
