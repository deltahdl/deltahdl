#include "common/system_functions.h"

#include <algorithm>
#include <string_view>

namespace delta {

bool IsStandardSystemFunction(std::string_view name) {
  static constexpr std::string_view kFunctions[] = {
      // §14.14, §16.14.7, §18.13 and §19.9.
      "$global_clock", "$inferred_clock", "$inferred_disable", "$urandom",
      "$urandom_range", "$get_coverage",
      // §20.3 and §20.4.
      "$realtime", "$stime", "$time", "$timeunit", "$timeprecision",
      // §20.5 and §20.6.
      "$bitstoreal", "$realtobits", "$bitstoshortreal", "$shortrealtobits",
      "$itor", "$rtoi", "$signed", "$unsigned", "$bits", "$isunbounded",
      "$typename",
      // §20.7.
      "$unpacked_dimensions", "$dimensions", "$left", "$right", "$low", "$high",
      "$increment", "$size",
      // §20.8.
      "$clog2", "$ln", "$log10", "$exp", "$sqrt", "$pow", "$floor", "$ceil",
      "$sin", "$cos", "$tan", "$asin", "$acos", "$atan", "$atan2", "$hypot",
      "$sinh", "$cosh", "$tanh", "$asinh", "$acosh", "$atanh",
      // §20.9.
      "$countbits", "$countones", "$onehot", "$onehot0", "$isunknown",
      // §20.12.
      "$sampled", "$rose", "$fell", "$stable", "$changed", "$past",
      "$past_gclk", "$rose_gclk", "$fell_gclk", "$stable_gclk", "$changed_gclk",
      "$future_gclk", "$rising_gclk", "$falling_gclk", "$steady_gclk",
      "$changing_gclk",
      // §20.13, §20.14 and §20.15.
      "$coverage_control", "$coverage_get_max", "$coverage_get",
      "$coverage_merge", "$coverage_save", "$random", "$dist_chi_square",
      "$dist_erlang", "$dist_exponential", "$dist_normal", "$dist_poisson",
      "$dist_t", "$dist_uniform", "$q_full",
      // §21.3 and §21.6.
      "$fopen", "$fgetc", "$ungetc", "$fgets", "$fscanf", "$sscanf", "$fread",
      "$ftell", "$fseek", "$rewind", "$feof", "$ferror", "$sformatf",
      "$test$plusargs", "$value$plusargs"};
  return std::ranges::any_of(kFunctions, [name](std::string_view function) {
    return function == name;
  });
}

}  // namespace delta
