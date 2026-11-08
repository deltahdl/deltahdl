#include <cctype>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <ios>
#include <optional>
#include <ostream>
#include <sstream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sdf_parser.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"

namespace delta {

SdfMtm ResolveSdfMtm(SdfMtmKeyword keyword, SdfMtm tool_default) {
  switch (keyword) {
    case SdfMtmKeyword::kMaximum:
      return SdfMtm::kMaximum;
    case SdfMtmKeyword::kMinimum:
      return SdfMtm::kMinimum;
    case SdfMtmKeyword::kTypical:
      return SdfMtm::kTypical;
    case SdfMtmKeyword::kToolControl:
      return tool_default;
  }
  return tool_default;
}

bool ParseSdfScaleType(std::string_view text, SdfScaleType& out) {
  if (text == "FROM_MTM") {
    out = SdfScaleType::kFromMtm;
    return true;
  }
  if (text == "FROM_MAXIMUM") {
    out = SdfScaleType::kFromMaximum;
    return true;
  }
  if (text == "FROM_MINIMUM") {
    out = SdfScaleType::kFromMinimum;
    return true;
  }
  if (text == "FROM_TYPICAL") {
    out = SdfScaleType::kFromTypical;
    return true;
  }
  return false;
}

static bool ParseRealAt(std::string_view text, std::size_t& pos, double& out) {
  while (pos < text.size() &&
         std::isspace(static_cast<unsigned char>(text[pos])) != 0) {
    ++pos;
  }
  std::size_t start = pos;
  if (pos < text.size() && (text[pos] == '+' || text[pos] == '-')) ++pos;
  bool saw_digit = false;
  while (pos < text.size() &&
         std::isdigit(static_cast<unsigned char>(text[pos])) != 0) {
    ++pos;
    saw_digit = true;
  }
  if (pos < text.size() && text[pos] == '.') {
    ++pos;
    while (pos < text.size() &&
           std::isdigit(static_cast<unsigned char>(text[pos])) != 0) {
      ++pos;
      saw_digit = true;
    }
  }
  if (!saw_digit) return false;
  out = std::stod(std::string(text.substr(start, pos - start)));
  return true;
}

bool ParseSdfScaleFactors(std::string_view text, SdfScaleFactors& out) {
  out = SdfScaleFactors{};
  if (text.empty()) return true;
  std::size_t pos = 0;
  double v = 0.0;
  if (!ParseRealAt(text, pos, v)) return false;
  out.min_factor = v;
  out.typ_factor = v;
  out.max_factor = v;
  while (pos < text.size() &&
         std::isspace(static_cast<unsigned char>(text[pos])) != 0) {
    ++pos;
  }
  if (pos >= text.size() || text[pos] != ':') return true;
  ++pos;
  if (!ParseRealAt(text, pos, v)) return false;
  out.typ_factor = v;
  out.max_factor = v;
  while (pos < text.size() &&
         std::isspace(static_cast<unsigned char>(text[pos])) != 0) {
    ++pos;
  }
  if (pos >= text.size() || text[pos] != ':') return true;
  ++pos;
  if (!ParseRealAt(text, pos, v)) return false;
  out.max_factor = v;
  return true;
}

static double ExactMagnitude(uint64_t whole, double real) {
  return real > 0.0 ? real : static_cast<double>(whole);
}

static uint64_t RoundToTicks(double scaled) {
  if (scaled <= 0.0) return 0;
  return static_cast<uint64_t>(std::floor(scaled + 0.5));
}

SdfDelayValue ApplySdfScaling(SdfDelayValue value, SdfScaleType type,
                              const SdfScaleFactors& factors) {
  double src_min = 0.0;
  double src_typ = 0.0;
  double src_max = 0.0;
  SdfDelayValue out;
  switch (type) {
    case SdfScaleType::kFromMtm:
      src_min = ExactMagnitude(value.min_val, value.min_real);
      src_typ = ExactMagnitude(value.typ_val, value.typ_real);
      src_max = ExactMagnitude(value.max_val, value.max_real);
      out.min_negative = value.min_negative;
      out.typ_negative = value.typ_negative;
      out.max_negative = value.max_negative;
      out.min_empty = value.min_empty;
      out.typ_empty = value.typ_empty;
      out.max_empty = value.max_empty;
      break;
    case SdfScaleType::kFromMinimum:
      src_min = src_typ = src_max =
          ExactMagnitude(value.min_val, value.min_real);
      out.min_negative = out.typ_negative = out.max_negative =
          value.min_negative;
      out.min_empty = out.typ_empty = out.max_empty = value.min_empty;
      break;
    case SdfScaleType::kFromTypical:
      src_min = src_typ = src_max =
          ExactMagnitude(value.typ_val, value.typ_real);
      out.min_negative = out.typ_negative = out.max_negative =
          value.typ_negative;
      out.min_empty = out.typ_empty = out.max_empty = value.typ_empty;
      break;
    case SdfScaleType::kFromMaximum:
      src_min = src_typ = src_max =
          ExactMagnitude(value.max_val, value.max_real);
      out.min_negative = out.typ_negative = out.max_negative =
          value.max_negative;
      out.min_empty = out.typ_empty = out.max_empty = value.max_empty;
      break;
  }
  out.empty = value.empty;
  out.min_real = src_min * factors.min_factor;
  out.typ_real = src_typ * factors.typ_factor;
  out.max_real = src_max * factors.max_factor;
  out.min_val = RoundToTicks(out.min_real);
  out.typ_val = RoundToTicks(out.typ_real);
  out.max_val = RoundToTicks(out.max_real);
  return out;
}

static void ScaleSdfDirections(std::vector<SdfIopathDirection>& directions,
                               SdfScaleType type,
                               const SdfScaleFactors& factors) {
  for (auto& dir : directions) {
    dir.delay = ApplySdfScaling(dir.delay, type, factors);
    dir.reject = ApplySdfScaling(dir.reject, type, factors);
    dir.error = ApplySdfScaling(dir.error, type, factors);
  }
}

static void ScaleSdfCell(SdfCell& cell, SdfScaleType type,
                         const SdfScaleFactors& factors) {
  for (auto& io : cell.iopaths) {
    io.rise = ApplySdfScaling(io.rise, type, factors);
    io.fall = ApplySdfScaling(io.fall, type, factors);
    io.turnoff = ApplySdfScaling(io.turnoff, type, factors);
    for (auto& v : io.values) v = ApplySdfScaling(v, type, factors);
    ScaleSdfDirections(io.directions, type, factors);
  }
  for (auto& tc : cell.timing_checks) {
    tc.limit = ApplySdfScaling(tc.limit, type, factors);
    tc.limit2 = ApplySdfScaling(tc.limit2, type, factors);
  }
  for (auto& sp : cell.specparams) {
    sp.value = ApplySdfScaling(sp.value, type, factors);
  }
  for (auto& ic : cell.interconnects) {
    ic.rise = ApplySdfScaling(ic.rise, type, factors);
    ic.fall = ApplySdfScaling(ic.fall, type, factors);
    for (auto& v : ic.values) v = ApplySdfScaling(v, type, factors);
    ScaleSdfDirections(ic.directions, type, factors);
  }
  for (auto& pl : cell.pulse_limits) {
    if (pl.is_percent) continue;
    pl.reject = ApplySdfScaling(pl.reject, type, factors);
    pl.error = ApplySdfScaling(pl.error, type, factors);
  }
  for (auto& dev : cell.devices) {
    dev.rise = ApplySdfScaling(dev.rise, type, factors);
    dev.fall = ApplySdfScaling(dev.fall, type, factors);
    dev.turnoff = ApplySdfScaling(dev.turnoff, type, factors);
    for (auto& v : dev.values) v = ApplySdfScaling(v, type, factors);
  }
}

static double SdfUnitRatio(double file_seconds, double precision_seconds) {
  if (precision_seconds <= 0.0) return 1.0;
  const double kFileUnit = file_seconds > 0.0 ? file_seconds : 1e-9;
  return kFileUnit / precision_seconds;
}

SdfFile ScaleSdfFile(const SdfFile& file, SdfScaleType type,
                     const SdfScaleFactors& factors) {
  SdfFile out = file;
  for (auto& cell : out.cells) ScaleSdfCell(cell, type, factors);
  return out;
}

static void WriteSdfCellLogEntries(std::ostream& out, const SdfCell& cell) {
  const std::string kPrefix = cell.cell_type + "/" + cell.instance + ": ";
  for (const auto& io : cell.iopaths) {
    out << kPrefix << "IOPATH " << io.src_port << " -> " << io.dst_port
        << " rise=" << io.rise.typ_val << " fall=" << io.fall.typ_val << '\n';
  }
  for (const auto& ic : cell.interconnects) {
    out << kPrefix << "INTERCONNECT " << ic.src_port << " -> " << ic.dst_port
        << " rise=" << ic.rise.typ_val << " fall=" << ic.fall.typ_val << '\n';
  }
  for (const auto& pl : cell.pulse_limits) {
    out << kPrefix << "PATHPULSE " << pl.src_port << " -> " << pl.dst_port
        << " reject=" << pl.reject.typ_val << " error=" << pl.error.typ_val
        << '\n';
  }
  for (const auto& tc : cell.timing_checks) {
    out << kPrefix << "TIMINGCHECK " << tc.data_port << " ref=" << tc.ref_port
        << " limit=" << tc.limit.typ_val << '\n';
  }
  for (const auto& sp : cell.specparams) {
    out << kPrefix << "SPECPARAM " << sp.name << " value=" << sp.value.typ_val
        << '\n';
  }
  for (const auto& dev : cell.devices) {
    out << kPrefix << "DEVICE "
        << (dev.port_instance.empty() ? "*" : dev.port_instance)
        << " rise=" << dev.rise.typ_val << " fall=" << dev.fall.typ_val << '\n';
  }
}

bool WriteSdfAnnotationLog(const SdfFile& file, std::string_view log_path,
                           std::string_view region_prefix,
                           std::string_view design_root) {
  if (log_path.empty()) return true;
  std::ofstream out{std::string(log_path), std::ios::app};
  if (!out.is_open()) return false;

  for (const auto& cell : file.cells) {
    if (!SdfCellPrefixInRegion(cell.instance, region_prefix, design_root))
      continue;
    WriteSdfCellLogEntries(out, cell);
  }
  return true;
}

ResolvedSdfAnnotateArgs ResolveSdfAnnotateArgs(
    std::string_view explicit_mtm_spec, std::string_view explicit_scale_factors,
    std::string_view explicit_scale_type, const SdfAnnotateConfig& config) {
  ResolvedSdfAnnotateArgs out;

  if (!config.mtm_spec.empty()) {
    ParseSdfMtmKeyword(config.mtm_spec, out.mtm);
  }
  if (!explicit_mtm_spec.empty()) {
    ParseSdfMtmKeyword(explicit_mtm_spec, out.mtm);
  }

  if (!config.scale_factors.empty()) {
    ParseSdfScaleFactors(config.scale_factors, out.factors);
  }
  if (!explicit_scale_factors.empty()) {
    ParseSdfScaleFactors(explicit_scale_factors, out.factors);
  }

  if (!config.scale_type.empty()) {
    ParseSdfScaleType(config.scale_type, out.scale_type);
  }
  if (!explicit_scale_type.empty()) {
    ParseSdfScaleType(explicit_scale_type, out.scale_type);
  }

  return out;
}

bool ReadSdfFile(std::string_view path, SdfFile& out) {
  if (path.empty()) return false;
  std::ifstream in{std::string(path)};
  if (!in.is_open()) return false;
  std::stringstream buffer;
  buffer << in.rdbuf();
  return ParseSdf(buffer.str(), out);
}

namespace {

struct SdfConfigLine {
  std::string keyword;
  std::string value;
};

SdfConfigLine SplitSdfConfigLine(std::string_view line) {
  const std::size_t kComment = line.find('#');
  if (kComment != std::string_view::npos) line = line.substr(0, kComment);
  const std::size_t kSlashes = line.find("//");
  if (kSlashes != std::string_view::npos) line = line.substr(0, kSlashes);
  const std::size_t kSemi = line.find(';');
  if (kSemi != std::string_view::npos) line = line.substr(0, kSemi);

  auto trim = [](std::string_view s) {
    while (!s.empty() && std::isspace(static_cast<unsigned char>(s.front()))) {
      s.remove_prefix(1);
    }
    while (!s.empty() && std::isspace(static_cast<unsigned char>(s.back()))) {
      s.remove_suffix(1);
    }
    return s;
  };

  line = trim(line);
  SdfConfigLine out;
  if (line.empty()) return out;
  const std::size_t kSplit = line.find_first_of(" \t=");
  if (kSplit == std::string_view::npos) {
    out.keyword = std::string(line);
    return out;
  }
  out.keyword = std::string(line.substr(0, kSplit));
  std::string_view rest = trim(line.substr(kSplit + 1));
  if (!rest.empty() && rest.front() == '=') rest = trim(rest.substr(1));
  if (rest.size() >= 2 && rest.front() == '"' && rest.back() == '"') {
    rest = rest.substr(1, rest.size() - 2);
  }
  out.value = std::string(rest);
  return out;
}

}  // namespace

bool ReadSdfAnnotateConfigFile(std::string_view path, SdfAnnotateConfig& out) {
  if (path.empty()) return false;
  std::ifstream in{std::string(path)};
  if (!in.is_open()) return false;

  std::string line;
  while (std::getline(in, line)) {
    const SdfConfigLine kEntry = SplitSdfConfigLine(line);
    if (kEntry.keyword == "MTM_SPEC") {
      out.mtm_spec = kEntry.value;
    } else if (kEntry.keyword == "SCALE_FACTORS") {
      out.scale_factors = kEntry.value;
    } else if (kEntry.keyword == "SCALE_TYPE") {
      out.scale_type = kEntry.value;
    }
  }
  return true;
}

static SdfFile ScaleSdfFileForRun(const SdfFile& file,
                                  const ResolvedSdfAnnotateArgs& resolved,
                                  double precision_seconds) {
  SdfScaleFactors factors = resolved.factors;
  const double kUnits = SdfUnitRatio(file.timescale_seconds, precision_seconds);
  factors.min_factor *= kUnits;
  factors.typ_factor *= kUnits;
  factors.max_factor *= kUnits;
  SdfFile scaled = ScaleSdfFile(file, resolved.scale_type, factors);
  if (kUnits == 1.0) return scaled;
  const SdfFile kPlain =
      ScaleSdfFile(file, resolved.scale_type, resolved.factors);
  for (std::size_t i = 0; i < scaled.cells.size(); ++i)
    scaled.cells[i].specparams = kPlain.cells[i].specparams;
  return scaled;
}

static void TranslateSdfCellPaths(SdfFile& file,
                                  const SdfAnnotateTaskArgs& args) {
  if (!args.instance_key_of_path) return;
  for (SdfCell& cell : file.cells) {
    std::optional<std::string> prefix = SdfCellPrefixInRegion(
        cell.instance, args.region_prefix, args.design_root);
    if (!prefix || prefix->empty()) continue;
    std::string_view path(*prefix);
    path.remove_suffix(1);
    std::string_view key = args.instance_key_of_path(path);
    if (key.empty()) continue;
    cell.instance = args.design_root + "." + std::string(key);
  }
}

SdfAnnotationResult RunSdfAnnotateTask(const SdfAnnotateTaskArgs& args,
                                       SpecifyManager& mgr,
                                       SdfMtm tool_default) {
  SdfAnnotationResult result;

  SdfFile file;
  if (!ReadSdfFile(args.sdf_file, file)) {
    result.warnings.push_back("SDF annotator: unable to read SDF file " +
                              args.sdf_file);
    return result;
  }
  TranslateSdfCellPaths(file, args);

  SdfAnnotateConfig config;
  if (!args.config_file.empty() &&
      !ReadSdfAnnotateConfigFile(args.config_file, config)) {
    result.warnings.push_back(
        "SDF annotator: unable to read configuration file " + args.config_file);
  }
  const ResolvedSdfAnnotateArgs kResolved = ResolveSdfAnnotateArgs(
      args.mtm_spec, args.scale_factors, args.scale_type, config);

  SdfMtmKeyword mtm_probe = SdfMtmKeyword::kToolControl;
  if (!args.mtm_spec.empty() && !ParseSdfMtmKeyword(args.mtm_spec, mtm_probe)) {
    result.warnings.push_back("SDF annotator: unknown mtm_spec " +
                              args.mtm_spec);
  }
  SdfScaleType type_probe = SdfScaleType::kFromMtm;
  if (!args.scale_type.empty() &&
      !ParseSdfScaleType(args.scale_type, type_probe)) {
    result.warnings.push_back("SDF annotator: unknown scale_type " +
                              args.scale_type);
  }

  const SdfFile kScaled =
      ScaleSdfFileForRun(file, kResolved, args.precision_seconds);
  const SdfMtm kMtm = ResolveSdfMtm(kResolved.mtm, tool_default);
  SdfAnnotationResult annotated = AnnotateSdfToManager(
      kScaled, mgr, kMtm, args.region_prefix, args.design_root);
  for (auto& warning : annotated.warnings) {
    result.warnings.push_back(std::move(warning));
  }

  if (!args.log_file.empty() &&
      !WriteSdfAnnotationLog(kScaled, args.log_file, args.region_prefix,
                             args.design_root)) {
    result.warnings.push_back("SDF annotator: unable to write log file " +
                              args.log_file);
  }
  return result;
}

std::string SdfAnnotateScopeName(const Expr* e, SimContext& ctx, Arena& arena) {
  if (e == nullptr) return {};
  switch (e->kind) {
    case ExprKind::kIdentifier: {
      std::string s;
      if (!e->scope_prefix.empty()) {
        s += std::string(e->scope_prefix);
        s += (e->scope_prefix == "$unit") ? "::" : ".";
      }
      s += std::string(e->text);
      return s;
    }
    case ExprKind::kMemberAccess:
      return SdfAnnotateScopeName(e->lhs, ctx, arena) + "." +
             (e->rhs != nullptr ? std::string(e->rhs->text) : std::string());
    case ExprKind::kSelect: {
      std::string s = SdfAnnotateScopeName(e->base, ctx, arena);
      if (e->index == nullptr) return s;
      const uint64_t kIndex = EvalExpr(e->index, ctx, arena).ToUint64();
      return s + "[" + std::to_string(kIndex) + "]";
    }
    default:
      break;
  }
  return std::string(e->text);
}

namespace {

std::string SdfRegionPrefix(std::string_view name, std::string_view design_root,
                            std::string_view caller_prefix) {
  constexpr std::string_view kRoot = "$root.";
  if (name.starts_with(kRoot)) name.remove_prefix(kRoot.size());
  if (name == design_root) return {};
  if (name.size() > design_root.size() && name.starts_with(design_root) &&
      name[design_root.size()] == '.') {
    return std::string(name.substr(design_root.size() + 1)) + ".";
  }
  return std::string(caller_prefix) + std::string(name) + ".";
}

std::string SdfAnnotateStringArg(const Expr* call, std::size_t index,
                                 SimContext& ctx, Arena& arena) {
  if (index >= call->args.size() || call->args[index] == nullptr) return {};
  return EvalStringArg(call->args[index], ctx, arena);
}

}  // namespace

static SdfMtm SdfMtmFromDelayMode(DelayMode mode) {
  switch (mode) {
    case DelayMode::kMin:
      return SdfMtm::kMinimum;
    case DelayMode::kMax:
      return SdfMtm::kMaximum;
    case DelayMode::kTyp:
      break;
  }
  return SdfMtm::kTypical;
}

bool EvalSdfAnnotateTask(const Expr* call, SimContext& ctx, Arena& arena) {
  if (call == nullptr) return false;
  SpecifyManager* mgr = ctx.GetSpecifyManager();
  if (mgr == nullptr) return false;

  SdfAnnotateTaskArgs args;
  args.sdf_file = SdfAnnotateStringArg(call, 0, ctx, arena);
  if (args.sdf_file.empty()) {
    ctx.GetDiag().Error(call->range.start,
                        "$sdf_annotate requires an SDF file name",
                        Subclause("32.9"));
    return false;
  }

  args.design_root = ctx.CurrentScopeName();
  args.precision_seconds =
      std::pow(10.0, static_cast<int>(ctx.GlobalPrecision()));

  if (call->args.size() > 1 && call->args[1] != nullptr) {
    args.module_instance = SdfAnnotateScopeName(call->args[1], ctx, arena);
    args.region_prefix = SdfRegionPrefix(args.module_instance, args.design_root,
                                         ctx.ActiveInstancePrefix());
  } else {
    args.module_instance = ctx.CurrentScopeName();
    args.region_prefix = ctx.ActiveInstancePrefix();
  }

  args.instance_key_of_path = [&ctx](std::string_view path) {
    return ctx.FindInstanceKeyOfPath(path);
  };
  args.config_file = SdfAnnotateStringArg(call, 2, ctx, arena);
  args.log_file = SdfAnnotateStringArg(call, 3, ctx, arena);
  args.mtm_spec = SdfAnnotateStringArg(call, 4, ctx, arena);
  args.scale_factors = SdfAnnotateStringArg(call, 5, ctx, arena);
  args.scale_type = SdfAnnotateStringArg(call, 6, ctx, arena);

  const SdfAnnotationResult kResult =
      RunSdfAnnotateTask(args, *mgr, SdfMtmFromDelayMode(ctx.GetDelayMode()));
  for (const auto& warning : kResult.warnings) {
    ctx.GetDiag().Warning(call->range.start, warning, Subclause("32.9"));
  }
  return true;
}

}  // namespace delta
