#pragma once

#include <cstddef>
#include <string>
#include <string_view>

namespace delta {

std::string EncodeBase64(std::string_view bytes);
bool DecodeBase64(std::string_view text, std::string* bytes);

std::string EncodeUuencode(std::string_view bytes, size_t line_length);
bool DecodeUuencode(std::string_view text, std::string* bytes);

std::string EncodeQuotedPrintable(std::string_view bytes, size_t line_length);
bool DecodeQuotedPrintable(std::string_view text, std::string* bytes);

std::string EncodeProtectBlockAlphabet(std::string_view bytes);
bool DecodeProtectBlockAlphabet(std::string_view text, std::string* bytes);

}  // namespace delta
