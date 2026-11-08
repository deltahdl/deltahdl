#pragma once

#include <cstdint>
#include <optional>
#include <string_view>

namespace delta {

struct Expr;
class SimContext;
class Arena;

std::string_view AnnexListingTheDistributionFunctions();

std::string_view SubclauseDefiningTheDistributionFunctionSyntax();

std::optional<std::string_view> CFunctionComputing(
    std::string_view sv_function);

int32_t RtlDistUniform(int32_t* seed, int32_t start, int32_t end);

int32_t RtlDistNormal(int32_t* seed, int32_t mean, int32_t sd);
int32_t RtlDistExponential(int32_t* seed, int32_t mean);
int32_t RtlDistPoisson(int32_t* seed, int32_t mean);
int32_t RtlDistChiSquare(int32_t* seed, int32_t df);
int32_t RtlDistT(int32_t* seed, int32_t df);
int32_t RtlDistErlang(int32_t* seed, int32_t k, int32_t mean);

int32_t RtlDistRound(double r);

int32_t RtlDistRandom(int32_t* seed);

void WriteBackDistributionSeed(const Expr* seed_arg, int32_t seed,
                               SimContext& ctx, Arena& arena);

}  // namespace delta
