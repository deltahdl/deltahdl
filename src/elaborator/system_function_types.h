#pragma once

#include <array>
#include <string_view>

#include "elaborator/typename_writer.h"

namespace delta {

struct SystemFunctionType {
  std::string_view name;
  SelfType type;
};

inline constexpr SelfType kIntegerResult = {32, true, true, true};
inline constexpr SelfType kIntResult = {32, true, false, true};
inline constexpr SelfType kIntUnsignedResult = {32, false, false, true};
inline constexpr SelfType kBitResult = {1, false, false, true};
inline constexpr SelfType kLogicBitResult = {1, false, true, true};
inline constexpr SelfType kVector64Result = {64, false, true, true};
inline constexpr SelfType kVector32Result = {32, false, true, true};

inline constexpr std::array kSystemFunctionTypes = {
    SystemFunctionType{"$bits", kIntegerResult},
    SystemFunctionType{"$left", kIntegerResult},
    SystemFunctionType{"$right", kIntegerResult},
    SystemFunctionType{"$low", kIntegerResult},
    SystemFunctionType{"$high", kIntegerResult},
    SystemFunctionType{"$increment", kIntegerResult},
    SystemFunctionType{"$size", kIntegerResult},
    SystemFunctionType{"$dimensions", kIntegerResult},
    SystemFunctionType{"$unpacked_dimensions", kIntegerResult},
    SystemFunctionType{"$clog2", kIntegerResult},
    SystemFunctionType{"$rtoi", kIntegerResult},
    SystemFunctionType{"$random", kIntegerResult},
    SystemFunctionType{"$dist_uniform", kIntegerResult},
    SystemFunctionType{"$dist_normal", kIntegerResult},
    SystemFunctionType{"$dist_exponential", kIntegerResult},
    SystemFunctionType{"$dist_poisson", kIntegerResult},
    SystemFunctionType{"$dist_chi_square", kIntegerResult},
    SystemFunctionType{"$dist_t", kIntegerResult},
    SystemFunctionType{"$dist_erlang", kIntegerResult},
    SystemFunctionType{"$countbits", kIntResult},
    SystemFunctionType{"$countones", kIntResult},
    SystemFunctionType{"$cast", kIntResult},
    SystemFunctionType{"$system", kIntResult},
    SystemFunctionType{"$urandom", kIntUnsignedResult},
    SystemFunctionType{"$urandom_range", kIntUnsignedResult},
    SystemFunctionType{"$onehot", kBitResult},
    SystemFunctionType{"$onehot0", kBitResult},
    SystemFunctionType{"$isunknown", kBitResult},
    SystemFunctionType{"$rose", kLogicBitResult},
    SystemFunctionType{"$fell", kLogicBitResult},
    SystemFunctionType{"$stable", kLogicBitResult},
    SystemFunctionType{"$changed", kLogicBitResult},
    SystemFunctionType{"$rose_gclk", kLogicBitResult},
    SystemFunctionType{"$fell_gclk", kLogicBitResult},
    SystemFunctionType{"$stable_gclk", kLogicBitResult},
    SystemFunctionType{"$changed_gclk", kLogicBitResult},
    SystemFunctionType{"$time", kVector64Result},
    SystemFunctionType{"$realtobits", kVector64Result},
    SystemFunctionType{"$stime", kVector32Result},
    SystemFunctionType{"$shortrealtobits", kVector32Result},
};

inline constexpr std::array<std::string_view, 4> kArgumentTypedFunctions = {
    "$sampled", "$past", "$past_gclk", "$future_gclk"};

inline constexpr std::array<std::string_view, 26> kRealSystemFunctions = {
    "$itor",     "$bitstoreal",  "$bitstoshortreal",
    "$realtime", "$ln",          "$log10",
    "$exp",      "$sqrt",        "$pow",
    "$floor",    "$ceil",        "$sin",
    "$cos",      "$tan",         "$asin",
    "$acos",     "$atan",        "$atan2",
    "$hypot",    "$sinh",        "$cosh",
    "$tanh",     "$asinh",       "$acosh",
    "$atanh",    "$get_coverage"};

}  // namespace delta
