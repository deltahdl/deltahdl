#include "simulator/probabilistic_distribution.h"

#include <cstdint>
#include <optional>
#include <string_view>

namespace delta {

std::string_view AnnexListingTheDistributionFunctions() { return "Annex N"; }

std::string_view SubclauseDefiningTheDistributionFunctionSyntax() {
  return "20.14";
}

std::optional<std::string_view> CFunctionComputing(
    std::string_view sv_function) {
  // §N.1, Table N.1, row by row.
  if (sv_function == "$dist_uniform") return "rtl_dist_uniform";
  if (sv_function == "$dist_normal") return "rtl_dist_normal";
  if (sv_function == "$dist_exponential") return "rtl_dist_exponential";
  if (sv_function == "$dist_poisson") return "rtl_dist_poisson";
  if (sv_function == "$dist_chi_square") return "rtl_dist_chi_square";
  if (sv_function == "$dist_t") return "rtl_dist_t";
  if (sv_function == "$dist_erlang") return "rtl_dist_erlang";
  if (sv_function == "$random") return "rtl_dist_uniform";
  return std::nullopt;
}

int32_t RtlDistRandom(int32_t* seed) {
  return RtlDistUniform(seed, INT32_MIN, INT32_MAX);
}

}  // namespace delta
