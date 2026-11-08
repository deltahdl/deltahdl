#ifndef DELTA_PREPROCESSOR_STANDARD_PRAGMAS_H
#define DELTA_PREPROCESSOR_STANDARD_PRAGMAS_H

#include <string_view>
#include <vector>

namespace delta {

inline constexpr std::string_view kResetPragmaName = "reset";
inline constexpr std::string_view kResetallPragmaName = "resetall";

const std::vector<std::string_view>& RecognizedPragmaNames();

bool IsRecognizedPragmaName(std::string_view name);

}  // namespace delta

#endif
