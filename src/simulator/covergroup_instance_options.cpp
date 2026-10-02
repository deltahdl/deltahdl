#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <string>
#include <string_view>
#include <utility>

#include "common/types.h"
#include "parser/ast_covergroup.h"
#include "simulator/coverage_types.h"
#include "simulator/covergroup_instance.h"
#include "simulator/covergroup_instance_internal.h"
#include "simulator/evaluation.h"

namespace delta {

namespace {

// The members of one level's option or type_option structure (§19.10), each
// under the name an option assignment gives it, grouped by the type its
// value takes: an int, a bit, a string or a real.
template <typename Options>
struct OptionFields {
  std::span<const std::pair<std::string_view, int32_t Options::*>> ints;
  std::span<const std::pair<std::string_view, bool Options::*>> bits;
  std::span<const std::pair<std::string_view, std::string Options::*>> strings;
  std::span<const std::pair<std::string_view, double Options::*>> reals;
};

template <typename Options, size_t N>
using IntFields =
    std::array<std::pair<std::string_view, int32_t Options::*>, N>;
template <typename Options, size_t N>
using BitFields = std::array<std::pair<std::string_view, bool Options::*>, N>;
template <typename Options, size_t N>
using StringFields =
    std::array<std::pair<std::string_view, std::string Options::*>, N>;
template <typename Options, size_t N>
using RealFields =
    std::array<std::pair<std::string_view, double Options::*>, N>;

// Table 19-1: the instance options of a covergroup.
constexpr IntFields<CoverOptions, 5> kGroupInts = {{
    {"weight", &CoverOptions::weight},
    {"goal", &CoverOptions::goal},
    {"at_least", &CoverOptions::at_least},
    {"auto_bin_max", &CoverOptions::auto_bin_max},
    {"cross_num_print_missing", &CoverOptions::cross_num_print_missing},
}};
constexpr BitFields<CoverOptions, 4> kGroupBits = {{
    {"cross_retain_auto_bins", &CoverOptions::cross_retain_auto_bins},
    {"detect_overlap", &CoverOptions::detect_overlap},
    {"per_instance", &CoverOptions::per_instance},
    {"get_inst_coverage", &CoverOptions::get_inst_coverage},
}};
constexpr StringFields<CoverOptions, 2> kGroupStrings = {{
    {"name", &CoverOptions::name},
    {"comment", &CoverOptions::comment},
}};

// Table 19-3: the type options of a covergroup.
constexpr IntFields<CoverGroupTypeOption, 2> kGroupTypeInts = {{
    {"weight", &CoverGroupTypeOption::weight},
    {"goal", &CoverGroupTypeOption::goal},
}};
constexpr BitFields<CoverGroupTypeOption, 3> kGroupTypeBits = {{
    {"strobe", &CoverGroupTypeOption::strobe},
    {"merge_instances", &CoverGroupTypeOption::merge_instances},
    {"distribute_first", &CoverGroupTypeOption::distribute_first},
}};
constexpr StringFields<CoverGroupTypeOption, 1> kGroupTypeStrings = {{
    {"comment", &CoverGroupTypeOption::comment},
}};
constexpr RealFields<CoverGroupTypeOption, 1> kGroupTypeReals = {{
    {"real_interval", &CoverGroupTypeOption::real_interval},
}};

// Table 19-2: the instance options of a coverpoint.
constexpr IntFields<CoverPointOption, 4> kPointInts = {{
    {"weight", &CoverPointOption::weight},
    {"goal", &CoverPointOption::goal},
    {"at_least", &CoverPointOption::at_least},
    {"auto_bin_max", &CoverPointOption::auto_bin_max},
}};
constexpr BitFields<CoverPointOption, 1> kPointBits = {{
    {"detect_overlap", &CoverPointOption::detect_overlap},
}};
constexpr StringFields<CoverPointOption, 1> kPointStrings = {{
    {"comment", &CoverPointOption::comment},
}};

// Table 19-4: the type options of a coverpoint.
constexpr IntFields<CoverPointTypeOption, 2> kPointTypeInts = {{
    {"weight", &CoverPointTypeOption::weight},
    {"goal", &CoverPointTypeOption::goal},
}};
constexpr StringFields<CoverPointTypeOption, 1> kPointTypeStrings = {{
    {"comment", &CoverPointTypeOption::comment},
}};
constexpr RealFields<CoverPointTypeOption, 1> kPointTypeReals = {{
    {"real_interval", &CoverPointTypeOption::real_interval},
}};

// Table 19-2: the instance options of a cross.
constexpr IntFields<CrossOption, 4> kCrossInts = {{
    {"weight", &CrossOption::weight},
    {"goal", &CrossOption::goal},
    {"at_least", &CrossOption::at_least},
    {"cross_num_print_missing", &CrossOption::cross_num_print_missing},
}};
constexpr BitFields<CrossOption, 1> kCrossBits = {{
    {"cross_retain_auto_bins", &CrossOption::cross_retain_auto_bins},
}};
constexpr StringFields<CrossOption, 1> kCrossStrings = {{
    {"comment", &CrossOption::comment},
}};

// Table 19-4: the type options of a cross.
constexpr IntFields<CrossTypeOption, 2> kCrossTypeInts = {{
    {"weight", &CrossTypeOption::weight},
    {"goal", &CrossTypeOption::goal},
}};
constexpr StringFields<CrossTypeOption, 1> kCrossTypeStrings = {{
    {"comment", &CrossTypeOption::comment},
}};

constexpr OptionFields<CoverOptions> kGroupFields = {
    kGroupInts, kGroupBits, kGroupStrings, {}};
constexpr OptionFields<CoverGroupTypeOption> kGroupTypeFields = {
    kGroupTypeInts, kGroupTypeBits, kGroupTypeStrings, kGroupTypeReals};
constexpr OptionFields<CoverPointOption> kPointFields = {
    kPointInts, kPointBits, kPointStrings, {}};
constexpr OptionFields<CoverPointTypeOption> kPointTypeFields = {
    kPointTypeInts, {}, kPointTypeStrings, kPointTypeReals};
constexpr OptionFields<CrossOption> kCrossFields = {
    kCrossInts, kCrossBits, kCrossStrings, {}};
constexpr OptionFields<CrossTypeOption> kCrossTypeFields = {
    kCrossTypeInts, {}, kCrossTypeStrings, {}};

// §19.7: sets the member an option assignment names to the value of its
// expression, evaluated when the covergroup is instantiated.
template <typename Options>
void SetOption(Options& options, const OptionFields<Options>& fields,
               const CoverageOption& option, SimContext& ctx, Arena& arena) {
  for (const auto& [name, field] : fields.ints) {
    if (name == option.member) {
      options.*field =
          static_cast<int32_t>(CovergroupInt(option.value, ctx, arena));
    }
  }
  for (const auto& [name, field] : fields.bits) {
    if (name == option.member) {
      options.*field = CovergroupInt(option.value, ctx, arena) != 0;
    }
  }
  for (const auto& [name, field] : fields.strings) {
    if (name == option.member) {
      options.*field = Logic4VecToString(EvalExpr(option.value, ctx, arena));
    }
  }
  for (const auto& [name, field] : fields.reals) {
    if (name == option.member) {
      options.*field = CovergroupReal(option.value, ctx, arena);
    }
  }
}

// §19.10: the value of an option member, an int as a signed 32-bit value, a
// bit as one bit, a string as a string and a real as a real.
template <typename Options>
bool ReadOption(const Options& options, const OptionFields<Options>& fields,
                std::string_view member, Arena& arena, Logic4Vec& out) {
  for (const auto& [name, field] : fields.ints) {
    if (name == member) {
      out = MakeLogic4VecVal(arena, 32, static_cast<uint32_t>(options.*field));
      out.is_signed = true;
      return true;
    }
  }
  for (const auto& [name, field] : fields.bits) {
    if (name == member) {
      out = MakeLogic4VecVal(arena, 1, options.*field ? 1 : 0);
      return true;
    }
  }
  for (const auto& [name, field] : fields.strings) {
    if (name == member) {
      out = StringToLogic4Vec(arena, options.*field);
      return true;
    }
  }
  for (const auto& [name, field] : fields.reals) {
    if (name == member) {
      out = MakeRealVec(arena, options.*field, 64);
      return true;
    }
  }
  return false;
}

}  // namespace

void ApplyGroupOption(CovergroupInstance& inst, const CoverageOption& option,
                      SimContext& ctx, Arena& arena) {
  if (option.is_type_option) {
    SetOption(inst.group->type_option, kGroupTypeFields, option, ctx, arena);
  } else {
    SetOption(inst.group->options, kGroupFields, option, ctx, arena);
  }
}

void ApplyPointOption(SampledCoverpoint& point, const CoverageOption& option,
                      SimContext& ctx, Arena& arena) {
  if (option.is_type_option) {
    SetOption(point.type_option, kPointTypeFields, option, ctx, arena);
  } else {
    SetOption(point.option, kPointFields, option, ctx, arena);
  }
}

void ApplyCrossOption(CrossCover& cross, const CoverageOption& option,
                      SimContext& ctx, Arena& arena) {
  if (option.is_type_option) {
    SetOption(cross.type_option, kCrossTypeFields, option, ctx, arena);
  } else {
    SetOption(cross.option, kCrossFields, option, ctx, arena);
  }
}

bool ReadGroupOption(const CoverGroup& group, bool type_option,
                     std::string_view member, Arena& arena, Logic4Vec& out) {
  return type_option
             ? ReadOption(group.type_option, kGroupTypeFields, member, arena,
                          out)
             : ReadOption(group.options, kGroupFields, member, arena, out);
}

bool ReadPointOption(const SampledCoverpoint& point, bool type_option,
                     std::string_view member, Arena& arena, Logic4Vec& out) {
  return type_option
             ? ReadOption(point.type_option, kPointTypeFields, member, arena,
                          out)
             : ReadOption(point.option, kPointFields, member, arena, out);
}

bool ReadCrossOption(const CrossCover& cross, bool type_option,
                     std::string_view member, Arena& arena, Logic4Vec& out) {
  return type_option
             ? ReadOption(cross.type_option, kCrossTypeFields, member, arena,
                          out)
             : ReadOption(cross.option, kCrossFields, member, arena, out);
}

}  // namespace delta
