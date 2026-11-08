#include "driver/cli_options.h"

#include <charconv>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <optional>
#include <sstream>
#include <string>
#include <string_view>
#include <system_error>
#include <utility>
#include <vector>

#include "common/arg_origin.h"
#include "common/types.h"
#include "preprocessor/protect_cli.h"
#include "simulator/foreign_code.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/sv_vpi_user.h"

namespace delta {

namespace {

void ParseDefine(std::string_view def, CliOptions& opts) {
  auto eq = def.find('=');
  if (eq == std::string_view::npos) {
    opts.defines.emplace_back(std::string(def), "1");
    return;
  }
  opts.defines.emplace_back(std::string(def.substr(0, eq)),
                            std::string(def.substr(eq + 1)));
}

struct ArgCursor {
  int& i;
  int argc;
  const char* const* argv;
  CliOptions& opts;
};

void ReportMissingValue(std::string_view name, int i, CliOptions& opts) {
  std::cerr << ArgOriginPrefix(opts.arg_origins, i) << name
            << " expects a value\n";
  opts.rejected_argument = true;
}

bool TakeValue(std::string_view arg, std::string_view name, ArgCursor cur,
               std::string& out) {
  if (arg != name) return false;
  if (cur.i + 1 >= cur.argc) {
    ReportMissingValue(name, cur.i, cur.opts);
    return true;
  }
  out = cur.argv[++cur.i];
  return true;
}

bool TakeValue(std::string_view arg, std::string_view name, ArgCursor cur,
               std::vector<std::string>& out) {
  if (arg != name) return false;
  if (cur.i + 1 >= cur.argc) {
    ReportMissingValue(name, cur.i, cur.opts);
    return true;
  }
  out.emplace_back(cur.argv[++cur.i]);
  return true;
}

ForeignCodeLocator LocatorInForce(const CliOptions& opts) {
  ForeignCodeLocator locator;
  locator.SetRoot(opts.sv_root);
  return locator;
}

bool TakeResolvedPath(std::string_view arg, std::string_view name,
                      ArgCursor cur, std::vector<std::string>& out) {
  const int kBefore = cur.i;
  std::string value;
  if (!TakeValue(arg, name, cur, value)) return false;
  if (cur.i == kBefore) return true;
  out.push_back(LocatorInForce(cur.opts).Resolve(value));
  return true;
}

bool TakeLibList(std::string_view arg, ArgCursor cur,
                 std::vector<ForeignCodeLibList>& out) {
  const int kBefore = cur.i;
  std::string value;
  if (!TakeValue(arg, ForeignCodeLibListSwitch(), cur, value)) return false;
  if (cur.i == kBefore) return true;
  const ForeignCodeLocator kLocator = LocatorInForce(cur.opts);
  out.push_back({kLocator.Resolve(value), kLocator.Root()});
  return true;
}

template <typename T>
bool TakeNumber(std::string_view arg, std::string_view name, ArgCursor cur,
                T& out) {
  if (arg != name) return false;
  if (cur.i + 1 >= cur.argc) {
    ReportMissingValue(name, cur.i, cur.opts);
    return true;
  }
  std::string_view text = cur.argv[++cur.i];
  if (text.starts_with("-")) {
    std::cerr << name << " expects a number that is not negative: " << text
              << "\n";
    cur.opts.rejected_argument = true;
    return true;
  }
  T value = 0;
  auto [stop, ec] =
      std::from_chars(text.data(), text.data() + text.size(), value);
  if (ec != std::errc() || stop != text.data() + text.size()) {
    std::cerr << name << " expects a number: " << text << "\n";
    cur.opts.rejected_argument = true;
    return true;
  }
  out = value;
  return true;
}

bool TryParseSimNumericArg(std::string_view arg, int& i, int argc,
                           const char* const argv[], CliOptions& opts) {
  ArgCursor cur{i, argc, argv, opts};
  if (TakeNumber(arg, "--seed", cur, opts.seed)) return true;
  return TakeNumber(arg, "--max-generate-iterations", cur,
                    opts.max_generate_iterations);
}

bool TryParseMinTypMaxArg(std::string_view arg, int& i, int argc,
                          const char* const argv[], CliOptions& opts) {
  if (arg != "--mintypmax") return false;
  if (i + 1 >= argc) {
    ReportMissingValue("--mintypmax", i, opts);
    return true;
  }
  std::string_view value = argv[i + 1];
  if (value == "min") {
    opts.mintypmax = delta::DelayMode::kMin;
  } else if (value == "typ") {
    opts.mintypmax = delta::DelayMode::kTyp;
  } else if (value == "max") {
    opts.mintypmax = delta::DelayMode::kMax;
  } else {
    std::cerr << "--mintypmax expects min, typ or max: " << value << "\n";
    opts.rejected_argument = true;
  }
  ++i;
  return true;
}

int VpiCompatModeNamed(std::string_view name) {
  static constexpr std::pair<std::string_view, int> kModes[] = {
      {"1364v1995", vpiMode1364v1995},
      {"1364v2001", vpiMode1364v2001},
      {"1364v2005", vpiMode1364v2005},
      {"1800v2005", vpiMode1800v2005},
      {"1800v2009", vpiMode1800v2009}};
  for (const auto& [spelling, mode] : kModes) {
    if (spelling == name) return mode;
  }
  return 0;
}

bool TryParseVpiCompatModeArg(std::string_view arg, int& i, int argc,
                              const char* const argv[], CliOptions& opts) {
  if (arg != "--vpi-compat-mode") return false;
  if (i + 1 >= argc) {
    ReportMissingValue("--vpi-compat-mode", i, opts);
    return true;
  }
  std::string_view value = argv[++i];
  int mode = VpiCompatModeNamed(value);
  if (mode == 0) {
    std::cerr << "--vpi-compat-mode expects 1364v1995, 1364v2001, 1364v2005, "
                 "1800v2005 or 1800v2009: "
              << value << "\n";
    opts.rejected_argument = true;
  } else if (opts.vpi_compat_mode != 0 && opts.vpi_compat_mode != mode) {
    std::cerr << "--vpi-compat-mode selects one default mode for the run; "
              << value << " follows another\n";
    opts.rejected_argument = true;
  } else {
    opts.vpi_compat_mode = mode;
  }
  return true;
}

bool TryParseSimArg(std::string_view arg, int& i, int argc,
                    const char* const argv[], CliOptions& opts) {
  ArgCursor cur{i, argc, argv, opts};
  if (TakeValue(arg, "--top", cur, opts.top_modules)) return true;
  if (TakeValue(arg, "--vcd", cur, opts.vcd_file)) return true;
  if (TryParseSimNumericArg(arg, i, argc, argv, opts)) return true;
  if (TryParseMinTypMaxArg(arg, i, argc, argv, opts)) return true;
  return TryParseVpiCompatModeArg(arg, i, argc, argv, opts);
}

bool TryParseGeneralFlag(std::string_view arg, CliOptions& opts) {
  if (arg == "--version") {
    opts.show_version = true;
    return true;
  }
  if (arg == "--help") {
    opts.show_help = true;
    return true;
  }
  if (arg == "--synth") {
    opts.synth_mode = true;
    return true;
  }
  if (arg == "--lint-only") {
    opts.lint_only = true;
    return true;
  }
  if (arg == "--compilation-unit-per-file") {
    opts.compilation_unit_per_file = true;
    return true;
  }
  if (arg == "--parse-only") {
    opts.parse_only = true;
    return true;
  }
  if (arg == "--dump-ast") {
    opts.dump_ast = true;
    return true;
  }
  if (arg == "--dump-ir") {
    opts.dump_ir = true;
    return true;
  }
  if (arg == "-Werror") {
    opts.werror = true;
    return true;
  }
  return false;
}

bool TryParseTimingCheckFlag(std::string_view arg, CliOptions& opts) {
  if (arg == "--negative-timing-checks") {
    opts.negative_timing_checks = true;
    return true;
  }
  if (arg == "--no-timing-checks") {
    opts.no_timing_checks = true;
    return true;
  }
  return false;
}

bool TryParsePulseStyleFlag(std::string_view arg, CliOptions& opts) {
  if (arg == "--pulse-style-onevent") {
    opts.pulse_style_ondetect = false;
    return true;
  }
  if (arg == "--pulse-style-ondetect") {
    opts.pulse_style_ondetect = true;
    return true;
  }
  if (arg == "--showcancelled") {
    opts.showcancelled = true;
    return true;
  }
  if (arg == "--noshowcancelled") {
    opts.showcancelled = false;
    return true;
  }
  return false;
}

bool TakePulseLimitPercent(std::string_view arg, std::string_view name,
                           ArgCursor cur, uint8_t& out) {
  const int kBefore = cur.i;
  uint32_t value = 0;
  if (!TakeNumber(arg, name, cur, value)) return false;
  if (cur.i == kBefore) return true;
  if (value > 100) {
    std::cerr << name
              << " expects a percentage from 0 to 100: " << cur.argv[cur.i]
              << "\n";
    cur.opts.rejected_argument = true;
    return true;
  }
  out = static_cast<uint8_t>(value);
  return true;
}

bool TryParsePulseLimitArg(std::string_view arg, int& i, int argc,
                           const char* const argv[], CliOptions& opts) {
  ArgCursor cur{i, argc, argv, opts};
  if (TakePulseLimitPercent(arg, "--pulse-reject-limit", cur,
                            opts.pulse_reject_percent)) {
    return true;
  }
  return TakePulseLimitPercent(arg, "--pulse-error-limit", cur,
                               opts.pulse_error_percent);
}

void SettlePulseLimitPercents(CliOptions& opts) {
  if (opts.pulse_error_percent >= opts.pulse_reject_percent) return;
  std::cerr << "error: --pulse-error-limit "
            << static_cast<unsigned>(opts.pulse_error_percent)
            << " is smaller than --pulse-reject-limit "
            << static_cast<unsigned>(opts.pulse_reject_percent)
            << "; the error limit percentage is taken as "
            << static_cast<unsigned>(opts.pulse_reject_percent) << "\n";
  opts.pulse_error_percent = opts.pulse_reject_percent;
}

bool TryParseSynthFlag(std::string_view arg, CliOptions& opts) {
  if (arg == "--dump-aig") {
    opts.dump_aig = true;
    return true;
  }
  if (arg == "--no-opt") {
    opts.no_opt = true;
    return true;
  }
  return false;
}

bool TryParseLibArg(std::string_view arg, int& i, int argc,
                    const char* const argv[], CliOptions& opts) {
  ArgCursor cur{i, argc, argv, opts};
  if (TakeValue(arg, "-L", cur, opts.lib_search_order)) return true;
  if (TakeValue(arg, "--config", cur, opts.config)) return true;
  if (TakeValue(arg, "--load-lib", cur, opts.precompiled_libs)) return true;
  if (TakeValue(arg, "--precompile-into", cur, opts.precompile_library)) {
    return true;
  }
  if (TakeValue(arg, "--precompile-out", cur, opts.precompile_output)) {
    return true;
  }
  if (TakeValue(arg, ForeignCodeRootSwitch(), cur, opts.sv_root)) return true;
  if (TakeResolvedPath(arg, ForeignCodeLibSwitch(), cur, opts.sv_libs)) {
    return true;
  }
  return TakeLibList(arg, cur, opts.sv_liblists);
}

bool TryParseDefineArg(std::string_view arg, int& i, int argc,
                       const char* const argv[], CliOptions& opts) {
  if (arg.starts_with("-D") && arg.size() > 2) {
    ParseDefine(arg.substr(2), opts);
    return true;
  }
  if (arg != "-D") return false;
  if (i + 1 >= argc) {
    ReportMissingValue("-D", i, opts);
    return true;
  }
  ParseDefine(argv[++i], opts);
  return true;
}

bool TryParseSingleArg(std::string_view arg, int& i, int argc,
                       const char* const argv[], CliOptions& opts) {
  if (TryParseGeneralFlag(arg, opts)) return true;
  if (TryParseTimingCheckFlag(arg, opts)) return true;
  if (TryParsePulseStyleFlag(arg, opts)) return true;
  if (TryParsePulseLimitArg(arg, i, argc, argv, opts)) return true;
  if (TryParseSynthFlag(arg, opts)) return true;
  if (TryParseDefineArg(arg, i, argc, argv, opts)) return true;
  if (TryParseSimArg(arg, i, argc, argv, opts)) return true;
  if (TryParseLibArg(arg, i, argc, argv, opts)) return true;
  if (delta::TryParseProtectArg(arg, i, argc, argv, opts.protect)) {
    if (opts.protect.rejected_argument) opts.rejected_argument = true;
    return true;
  }
  return false;
}

constexpr int kMaxOptionsFileDepth = 16;

bool ParseArgsAtDepth(int argc, char* argv[], CliOptions& opts, int depth);

bool ReadOptionsFile(const std::string& path, CliOptions& opts, int depth) {
  if (depth >= kMaxOptionsFileDepth) {
    std::cerr << "error: options files nest more than " << kMaxOptionsFileDepth
              << " deep at '" << path
              << "'; one of them names another that leads back to it\n";
    return false;
  }
  std::ifstream ifs(path);
  if (!ifs) {
    std::cerr << "error: cannot open options file '" << path << "'\n";
    return false;
  }
  std::vector<std::string> words;
  ArgOrigins origins;
  origins.path = path;
  origins.lines.push_back(0);
  std::string line;
  int line_no = 0;
  while (std::getline(ifs, line)) {
    ++line_no;
    std::istringstream words_of_line(line);
    std::string word;
    while (words_of_line >> word) {
      if (word.starts_with('#')) break;
      words.push_back(std::move(word));
      origins.lines.push_back(line_no);
    }
  }
  std::string program = "deltahdl";
  std::vector<char*> ptrs;
  ptrs.push_back(program.data());
  for (auto& w : words) {
    ptrs.push_back(w.data());
  }
  const ArgOrigins* outer = opts.arg_origins;
  opts.arg_origins = &origins;
  opts.protect.arg_origins = &origins;
  bool ok = ParseArgsAtDepth(static_cast<int>(ptrs.size()), ptrs.data(), opts,
                             depth + 1);
  opts.arg_origins = outer;
  opts.protect.arg_origins = outer;
  return ok;
}

bool TryParsePlusArg(std::string_view arg, CliOptions& opts) {
  if (arg.starts_with("+define+")) {
    ParseDefine(arg.substr(8), opts);
    return true;
  }
  if (arg.starts_with("+incdir+")) {
    opts.include_dirs.emplace_back(arg.substr(8));
    return true;
  }
  if (arg.starts_with("+")) {
    opts.plus_args.emplace_back(arg.substr(1));
    return true;
  }
  return false;
}

bool TakeOptionsFile(int& i, int argc, char* argv[], CliOptions& opts,
                     int depth) {
  if (i + 1 >= argc) {
    ReportMissingValue("-f", i, opts);
    return true;
  }
  return ReadOptionsFile(argv[++i], opts, depth);
}

bool ParseArgsAtDepth(int argc, char* argv[], CliOptions& opts, int depth) {
  for (int i = 1; i < argc; ++i) {
    std::string_view arg = argv[i];
    if (TryParseSingleArg(arg, i, argc, argv, opts)) continue;
    if (TryParsePlusArg(arg, opts)) continue;
    if (arg == "-f") {
      if (!TakeOptionsFile(i, argc, argv, opts, depth)) return false;
      continue;
    }
    if (arg.starts_with("-")) {
      std::cerr << ArgOriginPrefix(opts.arg_origins, i)
                << "unknown option: " << arg << "\n";
      return false;
    }
    if (arg.ends_with(".map")) {
      opts.library_map_files.emplace_back(arg);
      continue;
    }
    opts.source_files.emplace_back(arg);
  }
  return !opts.rejected_argument;
}

}  // namespace

bool ParseArgs(int argc, char* argv[], CliOptions& opts) {
  bool ok = ParseArgsAtDepth(argc, argv, opts, 0);
  SettlePulseLimitPercents(opts);
  return ok;
}

void ApplyPulseControlOptions(const CliOptions& opts, SpecifyManager& mgr) {
  mgr.SetGlobalPulseLimitPercents(opts.pulse_reject_percent,
                                  opts.pulse_error_percent);
  if (opts.pulse_style_ondetect.has_value()) {
    mgr.SetGlobalPulseStyle(*opts.pulse_style_ondetect ? PulseStyle::kOnDetect
                                                       : PulseStyle::kOnEvent);
  }
  if (opts.showcancelled.has_value()) {
    mgr.SetGlobalShowCancelled(*opts.showcancelled
                                   ? ShowCancelled::kShowcancelled
                                   : ShowCancelled::kNoshowcancelled);
  }
}

}  // namespace delta
