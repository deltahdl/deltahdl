#pragma once

#include <cstdint>
#include <optional>
#include <string_view>

namespace delta {

struct Expr;
class SimContext;
class Arena;

// Annex N: the algorithm for the probabilistic distribution functions. §N.1
// has the annex list the C source code of the SystemVerilog probabilistic
// distribution system functions, has Table N.1 cross-list each SystemVerilog
// function with the C function that computes it, and has §20.14 define the
// syntax of the functions; the algorithm is the C code §N.2 lists, which
// src/simulator/eval_math.cpp carries. This header states what §N.1 says and
// gives the base function of that code to the one caller outside
// eval_math.cpp that Table N.1 sends to it, $random.

// §N.1: the annex that lists the C source code of the distribution functions.
std::string_view AnnexListingTheDistributionFunctions();

// §N.1: the subclause that defines the syntax of the distribution functions.
std::string_view SubclauseDefiningTheDistributionFunctionSyntax();

// §N.1, Table N.1: the C function computing a SystemVerilog distribution
// function, or nothing for a name the table does not list. The seven $dist_
// functions each have a C function of their own name; $random has
// rtl_dist_uniform, called over the whole range of long.
std::optional<std::string_view> CFunctionComputing(
    std::string_view sv_function);

// §N.2 rtl_dist_uniform: the uniform draw over [start, end] that advances the
// seed, the reference's long being the 32-bit integer modeled here.
int32_t RtlDistUniform(int32_t* seed, int32_t start, int32_t end);

// §N.1, Table N.1: $random is rtl_dist_uniform(seed, LONG_MIN, LONG_MAX), a
// uniform draw over the whole 32-bit range that advances the seed.
int32_t RtlDistRandom(int32_t* seed);

// §20.14: the seed is an inout argument. Where the argument names a variable,
// the seed the algorithm advanced is written back to it, so that consecutive
// calls walk the stream and a seed re-assigned its first value replays it.
void WriteBackDistributionSeed(const Expr* seed_arg, int32_t seed,
                               SimContext& ctx, Arena& arena);

}  // namespace delta
