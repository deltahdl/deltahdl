#pragma once

#include <array>
#include <string_view>

#include "elaborator/typename_writer.h"

namespace delta {

// The types the standard gives the results of system functions, which the run
// sizes an operand by (§11.6.1) and the elaborator types a type reference to a
// call by (§6.23).

// The system functions whose result has a type of its own, each with that
// type: an integer for $bits (§20.6.2), the array query functions (§20.7),
// $clog2 (§20.8.1), $rtoi (§20.5), $random (§20.14.1) and the distribution
// functions (§20.14.2); an int for $countbits and $countones (§20.9), $cast
// called as a function (§6.24.2) and $system (§20.17.1); an int unsigned for
// $urandom and $urandom_range (§18.13); a bit for $onehot,
// $onehot0 and $isunknown (§20.9); a 1'b1 or 1'b0 for the value change
// functions (§16.9.3) and their global clocking forms (§16.9.4); a 64-bit time
// for $time (§20.3.1), a [63:0] for $realtobits (§20.5), a 32-bit unsigned
// time for $stime (§20.3.2) and a [31:0] for $shortrealtobits (§20.5).
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

// The sampled value functions whose result is their first argument's value at
// some clock tick, and so of its type: $sampled and $past (§16.9.3) and the
// global clocking $past_gclk and $future_gclk (§16.9.4).
inline constexpr std::array<std::string_view, 4> kArgumentTypedFunctions = {
    "$sampled", "$past", "$past_gclk", "$future_gclk"};

// The system functions returning a real value: $itor, $bitstoreal and
// $bitstoshortreal (§20.5), $realtime (§20.3.3), each function of Table 20-4
// (§20.8.2), and $get_coverage (§19.9).
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
