#pragma once

#include <string>
#include <string_view>

namespace delta {

std::string InterpretStringEscapes(std::string_view raw);

}
