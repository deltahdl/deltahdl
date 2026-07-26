#include <algorithm>
#include <array>
#include <cctype>
#include <cmath>
#include <cstddef>
#include <fstream>
#include <initializer_list>
#include <sstream>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
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

static uint64_t RoundToTicks(double scaled) {
  if (scaled <= 0.0) return 0;
  return static_cast<uint64_t>(std::floor(scaled + 0.5));
}

SdfDelayValue ApplySdfScaling(SdfDelayValue value, SdfScaleType type,
                              const SdfScaleFactors& factors) {
  double src_min = 0.0;
  double src_typ = 0.0;
  double src_max = 0.0;
  switch (type) {
    case SdfScaleType::kFromMtm:
      src_min = static_cast<double>(value.min_val);
      src_typ = static_cast<double>(value.typ_val);
      src_max = static_cast<double>(value.max_val);
      break;
    case SdfScaleType::kFromMinimum:
      src_min = src_typ = src_max = static_cast<double>(value.min_val);
      break;
    case SdfScaleType::kFromTypical:
      src_min = src_typ = src_max = static_cast<double>(value.typ_val);
      break;
    case SdfScaleType::kFromMaximum:
      src_min = src_typ = src_max = static_cast<double>(value.max_val);
      break;
  }
  SdfDelayValue out;
  out.min_val = RoundToTicks(src_min * factors.min_factor);
  out.typ_val = RoundToTicks(src_typ * factors.typ_factor);
  out.max_val = RoundToTicks(src_max * factors.max_factor);
  return out;
}

SdfFile ScaleSdfFile(const SdfFile& file, SdfScaleType type,
                     const SdfScaleFactors& factors) {
  SdfFile out = file;
  for (auto& cell : out.cells) {
    for (auto& io : cell.iopaths) {
      io.rise = ApplySdfScaling(io.rise, type, factors);
      io.fall = ApplySdfScaling(io.fall, type, factors);
      io.turnoff = ApplySdfScaling(io.turnoff, type, factors);
      io.rise_reject = ApplySdfScaling(io.rise_reject, type, factors);
      io.rise_error = ApplySdfScaling(io.rise_error, type, factors);
      io.fall_reject = ApplySdfScaling(io.fall_reject, type, factors);
      io.fall_error = ApplySdfScaling(io.fall_error, type, factors);
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
    }
    for (auto& pl : cell.pulse_limits) {
      pl.reject = ApplySdfScaling(pl.reject, type, factors);
      pl.error = ApplySdfScaling(pl.error, type, factors);
    }
    for (auto& dev : cell.devices) {
      dev.rise = ApplySdfScaling(dev.rise, type, factors);
      dev.fall = ApplySdfScaling(dev.fall, type, factors);
      dev.turnoff = ApplySdfScaling(dev.turnoff, type, factors);
    }
  }
  return out;
}

// §32.9: every individual annotation the file carries earns its own entry in
// the log file. §32.6 lets several SDF files be annotated in turn, and a later
// call naming the same log file adds its entries to the ones already there
// rather than replacing them, so the log reads as the record of the whole run.
bool WriteSdfAnnotationLog(const SdfFile& file, std::string_view log_path,
                           std::string_view scope) {
  if (log_path.empty()) return true;
  std::ofstream out{std::string(log_path), std::ios::app};
  if (!out.is_open()) return false;

  for (const auto& cell : file.cells) {
    // §32.9: the log records the annotations that were made, and a cell outside
    // the region the call named is never annotated, so it earns no entry.
    if (!CellInScope(cell.instance, scope)) continue;
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
    // A DEVICE entry is annotated like any other delay, so it earns an entry of
    // its own. An entry that names no port instance reaches every output of the
    // cell, which is what the empty target stands for here.
    for (const auto& dev : cell.devices) {
      out << kPrefix << "DEVICE "
          << (dev.port_instance.empty() ? "*" : dev.port_instance)
          << " rise=" << dev.rise.typ_val << " fall=" << dev.fall.typ_val
          << '\n';
    }
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

// One configuration-file line reduced to the keyword it names and the text that
// follows. A line that names nothing leaves `keyword` empty.
struct SdfConfigLine {
  std::string keyword;
  std::string value;
};

SdfConfigLine SplitSdfConfigLine(std::string_view line) {
  // A comment runs to the end of the line, and a trailing ';' closes an entry.
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
  // The value may be quoted, as the same text is a quoted argument when it is
  // written on the $sdf_annotate call instead.
  if (rest.size() >= 2 && rest.front() == '"' && rest.back() == '"') {
    rest = rest.substr(1, rest.size() - 2);
  }
  out.value = std::string(rest);
  return out;
}

}  // namespace

// §32.9: the configuration file controls the same aspects of annotation the
// call's own arguments do. The three the call can also name -- MTM_SPEC,
// SCALE_FACTORS and SCALE_TYPE -- are read here; ResolveSdfAnnotateArgs is what
// then lets an argument written on the call override the keyword read here.
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

SdfAnnotationResult RunSdfAnnotateTask(const SdfAnnotateTaskArgs& args,
                                       SpecifyManager& mgr,
                                       SdfMtm tool_default) {
  SdfAnnotationResult result;

  // §32.6: each call is one annotation of the design from one SDF file, so the
  // call is recorded on the manager whether or not the file turns out to be
  // readable. That record is what makes a run of several calls, each over its
  // own file and its own region, visible as such.
  mgr.AnnotateSdf({args.sdf_file, args.module_instance});

  SdfFile file;
  if (!ReadSdfFile(args.sdf_file, file)) {
    result.warnings.push_back("SDF annotator: unable to read SDF file " +
                              args.sdf_file);
    return result;
  }

  // §32.9: the configuration file is read first, then whichever of mtm_spec,
  // scale_factors and scale_type the call wrote overrides the matching keyword
  // in it.
  SdfAnnotateConfig config;
  if (!args.config_file.empty() &&
      !ReadSdfAnnotateConfigFile(args.config_file, config)) {
    result.warnings.push_back(
        "SDF annotator: unable to read configuration file " + args.config_file);
  }
  const ResolvedSdfAnnotateArgs kResolved = ResolveSdfAnnotateArgs(
      args.mtm_spec, args.scale_factors, args.scale_type, config);

  // §32.9: an mtm_spec or scale_type the annotator does not know is not one of
  // the keywords Table 32-5 / Table 32-6 lists, so it is reported rather than
  // quietly taken as the default it left in place.
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
      ScaleSdfFile(file, kResolved.scale_type, kResolved.factors);
  const SdfMtm kMtm = ResolveSdfMtm(kResolved.mtm, tool_default);
  SdfAnnotationResult annotated =
      AnnotateSdfToManager(kScaled, mgr, kMtm, args.module_instance);
  for (auto& warning : annotated.warnings) {
    result.warnings.push_back(std::move(warning));
  }

  // §32.9: with a log_file named, each individual annotation the file carries
  // is written out as its own entry.
  if (!args.log_file.empty() &&
      !WriteSdfAnnotationLog(kScaled, args.log_file, args.module_instance)) {
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
      // §32.9: array indices are permitted in a module_instance, so an indexed
      // element of an instance array names its own level of the hierarchy. The
      // index is evaluated, which is what lets it be written as anything that
      // reduces to a value rather than only as a plain number.
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

// §32.9: read one operand of a $sdf_annotate call as a character string. An
// operand the call skipped over on its way to a later one is absent here and
// reads as no text at all, which is the same as leaving it off the end.
std::string SdfAnnotateStringArg(const Expr* call, std::size_t index,
                                 SimContext& ctx, Arena& arena) {
  if (index >= call->args.size() || call->args[index] == nullptr) return {};
  return EvalStringArg(call->args[index], ctx, arena);
}

}  // namespace

bool EvalSdfAnnotateTask(const Expr* call, SimContext& ctx, Arena& arena) {
  if (call == nullptr) return false;
  SpecifyManager* mgr = ctx.GetSpecifyManager();
  if (mgr == nullptr) return false;

  SdfAnnotateTaskArgs args;
  // §32.9: sdf_file is the one required operand. It is an expression, so it may
  // be written as a string literal, held in a `string` variable, or held in an
  // integral variable whose bytes spell the name.
  args.sdf_file = SdfAnnotateStringArg(call, 0, ctx, arena);
  if (args.sdf_file.empty()) {
    ctx.GetDiag().Error(call->range.start,
                        "$sdf_annotate requires an SDF file name");
    return false;
  }

  // §32.9: module_instance names a level of the design hierarchy rather than a
  // readable value, so it is taken as the name it writes. Left out, the
  // annotator works from the module that holds the call.
  if (call->args.size() > 1 && call->args[1] != nullptr) {
    args.module_instance = SdfAnnotateScopeName(call->args[1], ctx, arena);
  } else {
    args.module_instance = ctx.CurrentScopeName();
  }

  args.config_file = SdfAnnotateStringArg(call, 2, ctx, arena);
  args.log_file = SdfAnnotateStringArg(call, 3, ctx, arena);
  args.mtm_spec = SdfAnnotateStringArg(call, 4, ctx, arena);
  args.scale_factors = SdfAnnotateStringArg(call, 5, ctx, arena);
  args.scale_type = SdfAnnotateStringArg(call, 6, ctx, arena);

  const SdfAnnotationResult kResult = RunSdfAnnotateTask(args, *mgr);
  for (const auto& warning : kResult.warnings) {
    ctx.GetDiag().Warning(call->range.start, warning);
  }
  return true;
}

}  // namespace delta
