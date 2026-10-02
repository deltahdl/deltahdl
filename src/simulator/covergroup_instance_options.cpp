#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/coverage_types.h"
#include "simulator/covergroup_instance.h"
#include "simulator/covergroup_instance_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

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

// §19.7: sets the option `member` to `value`, an int as an integral value, a
// bit as true where nonzero, a string as a string and a real as a real.
template <typename Options>
void SetOptionValue(Options& options, const OptionFields<Options>& fields,
                    std::string_view member, const Logic4Vec& value) {
  for (const auto& [name, field] : fields.ints) {
    if (name == member) {
      options.*field = static_cast<int32_t>(CovergroupIntOf(value));
    }
  }
  for (const auto& [name, field] : fields.bits) {
    if (name == member) options.*field = CovergroupIntOf(value) != 0;
  }
  for (const auto& [name, field] : fields.strings) {
    if (name == member) options.*field = Logic4VecToString(value);
  }
  for (const auto& [name, field] : fields.reals) {
    if (name == member) options.*field = CovergroupRealOf(value);
  }
}

// §19.7: sets the member an option assignment names to the value of its
// expression, evaluated when the covergroup is instantiated.
template <typename Options>
void SetOption(Options& options, const OptionFields<Options>& fields,
               const CoverageOption& option, SimContext& ctx, Arena& arena) {
  SetOptionValue(options, fields, option.member,
                 EvalExpr(option.value, ctx, arena));
}

// §19.7: the instance options an assignment after instantiation may set;
// per_instance and get_inst_coverage are set in the covergroup definition
// only, and auto_bin_max, detect_overlap and cross_retain_auto_bins in the
// covergroup or coverpoint definition only.
constexpr std::array<std::string_view, 6> kProcedurallyAssignable = {
    "name", "weight", "goal", "comment", "at_least", "cross_num_print_missing"};

bool ProcedurallyAssignable(std::string_view member) {
  return std::ranges::find(kProcedurallyAssignable, member) !=
         kProcedurallyAssignable.end();
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

// §19.7: writes `value` to the instance option `member` of a coverpoint or a
// cross, whose new weight and at_least take effect in its coverage at once.
void SetPointOptionValue(SampledCoverpoint& point, std::string_view member,
                         const Logic4Vec& value) {
  SetOptionValue(point.option, kPointFields, member, value);
  point.point->weight = point.option.weight;
  for (CoverBin& bin : point.point->bins) {
    bin.at_least = static_cast<uint32_t>(std::max(0, point.option.at_least));
  }
}

void SetCrossOptionValue(CrossCover& cross, std::string_view member,
                         const Logic4Vec& value) {
  SetOptionValue(cross.option, kCrossFields, member, value);
  for (CrossBin& bin : cross.bins) {
    bin.at_least = static_cast<uint32_t>(std::max(0, cross.option.at_least));
  }
}

// §19.7: whether a coverpoint or cross sets the option `member` itself, in
// its definition or by an assignment to it, so that the covergroup's value of
// it is not its default.
bool SetsOwnOption(const std::vector<std::string_view>& own,
                   std::string_view member) {
  return std::ranges::find(own, member) != own.end();
}

// §19.7.1: the type option assignments of the item `index` of a covergroup
// definition where it is the coverpoint or cross `item`, added to `found`;
// whether it is that item.
bool ItemTypeOptions(const CoverageSpecOrOption& spec, size_t index,
                     std::string_view item,
                     std::vector<const CoverageOption*>& found) {
  if (spec.kind == CoverageSpecKind::kCoverPoint &&
      CoverpointName(*spec.cover_point, index) == item) {
    for (const BinsOrOptions& bins : spec.cover_point->bins) {
      if (bins.kind == BinsOrOptionsKind::kOption)
        found.push_back(&bins.option);
    }
    return true;
  }
  if (spec.kind == CoverageSpecKind::kCoverCross &&
      spec.cover_cross->label == item) {
    for (const CrossBodyItem& body : spec.cover_cross->body) {
      if (body.kind == CrossBodyItemKind::kOption)
        found.push_back(&body.option);
    }
    return true;
  }
  return false;
}

// §19.7.1: a type option named through the covergroup type `decl`, of the
// covergroup where `item` is empty and else of its coverpoint or cross `item`.
struct TypeOptionName {
  const CovergroupDecl* decl = nullptr;
  std::string_view item;
  std::string_view member;
};

// §19.7.1: the type option assignments a definition gives one level of a
// covergroup type, `defined`, and the type options written through the type
// since, `writes`.
struct DefinedTypeOptions {
  std::vector<const CoverageOption*> defined;
  std::vector<const TypeOptionWrite*> writes;
};

// §19.7.1: the type options of one level, starting from the defaults of
// Table 19-3 in `options`, as `set` gives them.
template <typename Options>
Options DefinedOptions(Options options, const OptionFields<Options>& fields,
                       const DefinedTypeOptions& set, SimContext& ctx,
                       Arena& arena) {
  for (const CoverageOption* option : set.defined) {
    if (option->is_type_option) SetOption(options, fields, *option, ctx, arena);
  }
  for (const TypeOptionWrite* write : set.writes) {
    SetOptionValue(options, fields, write->member, write->value);
  }
  return options;
}

// §19.7.1: the type option `name`, as its definition and the writes through
// the type since give it, where no instance of the type has been built to
// read it from.
bool ReadDefinedTypeOption(const TypeOptionName& name, SimContext& ctx,
                           Arena& arena, Logic4Vec& out) {
  DefinedTypeOptions set;
  for (const TypeOptionWrite& write : ctx.Covergroups().TypeOptionWrites()) {
    if (write.decl == name.decl && write.item == name.item) {
      set.writes.push_back(&write);
    }
  }
  const CovergroupDecl& decl = *name.decl;
  for (size_t i = 0; i < decl.items.size(); ++i) {
    const CoverageSpecOrOption& spec = decl.items[i];
    if (name.item.empty()) {
      if (spec.kind == CoverageSpecKind::kOption)
        set.defined.push_back(&spec.option);
      continue;
    }
    if (!ItemTypeOptions(spec, i, name.item, set.defined)) continue;
    if (spec.kind == CoverageSpecKind::kCoverCross) {
      return ReadOption(
          DefinedOptions(CrossTypeOption{}, kCrossTypeFields, set, ctx, arena),
          kCrossTypeFields, name.member, arena, out);
    }
    return ReadOption(DefinedOptions(CoverPointTypeOption{}, kPointTypeFields,
                                     set, ctx, arena),
                      kPointTypeFields, name.member, arena, out);
  }
  return name.item.empty() &&
         ReadOption(DefinedOptions(CoverGroupTypeOption{}, kGroupTypeFields,
                                   set, ctx, arena),
                    kGroupTypeFields, name.member, arena, out);
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
    point.point->type_weight = point.type_option.weight;
  } else {
    SetOption(point.option, kPointFields, option, ctx, arena);
    point.own_options.push_back(option.member);
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

void WriteGroupOption(CovergroupInstance& inst, std::string_view member,
                      const Logic4Vec& value) {
  if (!ProcedurallyAssignable(member)) return;
  SetOptionValue(inst.group->options, kGroupFields, member, value);
  if (member != "at_least" && member != "cross_num_print_missing") return;
  for (SampledCoverpoint& point : inst.points) {
    if (!SetsOwnOption(point.own_options, member)) {
      SetPointOptionValue(point, member, value);
    }
  }
  for (SampledCross& cross : inst.crosses) {
    if (!SetsOwnOption(cross.own_options, member)) {
      SetCrossOptionValue(inst.group->crosses[cross.index], member, value);
    }
  }
}

void WritePointOption(SampledCoverpoint& point, std::string_view member,
                      const Logic4Vec& value) {
  if (!ProcedurallyAssignable(member)) return;
  point.own_options.push_back(member);
  SetPointOptionValue(point, member, value);
}

void WriteCrossOption(CovergroupInstance& inst, SampledCross& cross,
                      std::string_view member, const Logic4Vec& value) {
  if (!ProcedurallyAssignable(member)) return;
  cross.own_options.push_back(member);
  SetCrossOptionValue(inst.group->crosses[cross.index], member, value);
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

void SetTypeOption(CovergroupInstance& inst, const TypeOptionWrite& write) {
  if (write.item.empty()) {
    SetOptionValue(inst.group->type_option, kGroupTypeFields, write.member,
                   write.value);
    return;
  }
  for (SampledCoverpoint& point : inst.points) {
    if (point.point->name != write.item) continue;
    SetOptionValue(point.type_option, kPointTypeFields, write.member,
                   write.value);
    point.point->type_weight = point.type_option.weight;
  }
  for (CrossCover& cross : inst.group->crosses) {
    if (cross.name != write.item) continue;
    SetOptionValue(cross.type_option, kCrossTypeFields, write.member,
                   write.value);
  }
}

bool ReadTypeOption(const CovergroupInstance& inst, std::string_view item,
                    std::string_view member, Arena& arena, Logic4Vec& out) {
  if (item.empty()) {
    return ReadGroupOption(*inst.group, true, member, arena, out);
  }
  for (const SampledCoverpoint& point : inst.points) {
    if (point.point->name == item) {
      return ReadPointOption(point, true, member, arena, out);
    }
  }
  for (const CrossCover& cross : inst.group->crosses) {
    if (cross.name == item) {
      return ReadCrossOption(cross, true, member, arena, out);
    }
  }
  return false;
}

void CovergroupTable::WriteTypeOption(TypeOptionWrite write) {
  for (auto& [key, inst] : instances_) {
    (void)key;
    if (inst.decl == write.decl) SetTypeOption(inst, write);
  }
  type_option_writes_.push_back(std::move(write));
}

void CovergroupTable::TakeTypeOptionWrites(CovergroupInstance& inst) const {
  for (const TypeOptionWrite& write : type_option_writes_) {
    if (write.decl == inst.decl) SetTypeOption(inst, write);
  }
}

const CovergroupInstance* CovergroupTable::AnyOf(
    const CovergroupDecl* decl) const {
  for (const auto& [key, inst] : instances_) {
    (void)key;
    if (inst.decl == decl) return &inst;
  }
  return nullptr;
}

// §19.7.1: `cg::type_option.member = ...;` and `cg::x::type_option.member =
// ...;`, where `access` is the `cg::type_option` or `cg::x::type_option` the
// member is selected from.
bool TryCovergroupTypeOptionAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  const Expr* lhs = stmt->lhs;
  if (lhs == nullptr || stmt->rhs == nullptr ||
      lhs->kind != ExprKind::kMemberAccess || lhs->rhs == nullptr ||
      lhs->lhs == nullptr || lhs->lhs->kind != ExprKind::kMemberAccess) {
    return false;
  }
  TypeOptionWrite write;
  write.decl = TypeOptionOwner(lhs->lhs, ctx, write.item);
  if (write.decl == nullptr) return false;
  write.member = std::string(lhs->rhs->text);
  // §19.7.1: strobe and real_interval are set in the definition only.
  if (write.member == "strobe" || write.member == "real_interval") return true;
  write.value = EvalExpr(stmt->rhs, ctx, arena);
  ctx.Covergroups().WriteTypeOption(std::move(write));
  return true;
}

bool TryEvalCovergroupTypeOptionRead(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out) {
  std::string item;
  const CovergroupDecl* decl = TypeOptionOwner(expr->lhs, ctx, item);
  if (decl == nullptr) return false;
  const CovergroupInstance* inst = ctx.Covergroups().AnyOf(decl);
  if (inst == nullptr) {
    return ReadDefinedTypeOption({decl, item, expr->rhs->text}, ctx, arena,
                                 out);
  }
  return ReadTypeOption(*inst, item, expr->rhs->text, arena, out);
}

}  // namespace delta
