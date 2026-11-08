#pragma once

#include <string>
#include <string_view>

namespace delta {

std::string Sha1Digest(std::string_view bytes);

std::string Md5Digest(std::string_view bytes);

}  // namespace delta
