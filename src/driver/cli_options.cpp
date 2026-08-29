#include "driver/cli_options.h"

#include <charconv>
#include <fstream>
#include <iostream>
#include <string>
#include <string_view>
#include <system_error>
#include <utility>
#include <vector>

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

// One reading of a command line: where it has got to, how far it can go, the
// arguments themselves, and what it has filled in. It travels as one value so
// that a helper taking a destination as well stays inside the five parameters
// readability-function-size.ParameterThreshold allows in
// etc/clang_tidy/src.yml.
struct ArgCursor {
  int& i;
  int argc;
  const char* const* argv;
  CliOptions& opts;
};

// Reports an option that was recognized and whose value the command line ended
// before, and fails the parse through CliOptions::rejected_argument.
//
// The option is not an unrecognized one and must not be reported as one.
// ParseArgs prints "unknown option" for an argument no parser took, and an
// option written last with its value left off would reach that branch if the
// parsers answered only "this is not my option"; the user would then be told
// the option does not exist. Issue #3426 is that they were.
void ReportMissingValue(std::string_view name, CliOptions& opts) {
  std::cerr << name << " expects a value\n";
  opts.rejected_argument = true;
}

// Whether `arg` is the option `name`, taking its value into `out` where the
// command line carried one. The answer is the same for an option whose value is
// missing: it was this option, and ReportMissingValue has said what is wrong
// with it.
bool TakeValue(std::string_view arg, std::string_view name, ArgCursor cur,
               std::string& out) {
  if (arg != name) return false;
  if (cur.i + 1 >= cur.argc) {
    ReportMissingValue(name, cur.opts);
    return true;
  }
  out = cur.argv[++cur.i];
  return true;
}

// The same for an option a command line may write more than once, whose values
// are kept in the order they were written.
bool TakeValue(std::string_view arg, std::string_view name, ArgCursor cur,
               std::vector<std::string>& out) {
  if (arg != name) return false;
  if (cur.i + 1 >= cur.argc) {
    ReportMissingValue(name, cur.opts);
    return true;
  }
  out.emplace_back(cur.argv[++cur.i]);
  return true;
}

// The same for an option whose value is a number.
//
// std::from_chars answers whether the text was a number rather than throwing
// for one that was not, which std::stoull and its siblings do: nothing caught
// those, so a mistyped number terminated the process instead of being reported.
// The whole of the value has to be consumed, so a number with anything after it
// is refused rather than read up to the first character that is not a digit.
template <typename T>
bool TakeNumber(std::string_view arg, std::string_view name, ArgCursor cur,
                T& out) {
  if (arg != name) return false;
  if (cur.i + 1 >= cur.argc) {
    ReportMissingValue(name, cur.opts);
    return true;
  }
  std::string_view text = cur.argv[++cur.i];
  // Every option read here is a count: a simulation time, a seed, an iteration
  // budget and a LUT input count. None of them has a meaning below zero, and
  // std::from_chars would take a negative value into the one signed field
  // without complaint, so the sign is refused before the digits are read.
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

// The simulation options whose argument is a number rather than a name, split
// out from TryParseSimArg below so that neither function's branch count grows
// with the other's. A caller reaches these through TryParseSimArg; the split is
// not visible on the command line.
bool TryParseSimNumericArg(std::string_view arg, int& i, int argc,
                           const char* const argv[], CliOptions& opts) {
  ArgCursor cur{i, argc, argv, opts};
  if (TakeNumber(arg, "--max-time", cur, opts.max_time)) return true;
  if (TakeNumber(arg, "--seed", cur, opts.seed)) return true;
  return TakeNumber(arg, "--max-generate-iterations", cur,
                    opts.max_generate_iterations);
}

// §11.11's min:typ:max selection, split out of TryParseSimArg below for the
// same reason TryParseSimNumericArg is: neither function's branch count grows
// with the other's. A caller reaches it through TryParseSimArg; the split is
// not visible on the command line.
//
// A value that is none of the three is consumed rather than left behind, and
// answers true after setting CliOptions::rejected_argument. Answering false
// would hand --mintypmax back to ParseArgs, which knows only that no parser
// took it and would report the option as unrecognized after this function had
// already printed what is actually wrong with it. A --mintypmax written with no
// value at all is answered the same way, for the same reason.
bool TryParseMinTypMaxArg(std::string_view arg, int& i, int argc,
                          const char* const argv[], CliOptions& opts) {
  if (arg != "--mintypmax") return false;
  if (i + 1 >= argc) {
    ReportMissingValue("--mintypmax", opts);
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

bool TryParseSimArg(std::string_view arg, int& i, int argc,
                    const char* const argv[], CliOptions& opts) {
  ArgCursor cur{i, argc, argv, opts};
  if (TakeValue(arg, "--top", cur, opts.top_module)) return true;
  if (TakeValue(arg, "--vcd", cur, opts.vcd_file)) return true;
  if (TakeValue(arg, "-o", cur, opts.output_file)) return true;
  if (TakeValue(arg, "--timescale", cur, opts.timescale)) return true;
  if (TakeValue(arg, "--fst", cur, opts.fst_file)) return true;
  if (TryParseSimNumericArg(arg, i, argc, argv, opts)) return true;
  return TryParseMinTypMaxArg(arg, i, argc, argv, opts);
}

bool TryParseSynthArg(std::string_view arg, int& i, int argc,
                      const char* const argv[], CliOptions& opts) {
  ArgCursor cur{i, argc, argv, opts};
  if (TakeValue(arg, "--target", cur, opts.target)) return true;
  if (TakeNumber(arg, "--lut-size", cur, opts.lut_size)) return true;
  if (TakeValue(arg, "--lib", cur, opts.lib_file)) return true;
  return TakeValue(arg, "--format", cur, opts.format);
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
  if (arg == "--dump-ast") {
    opts.dump_ast = true;
    return true;
  }
  if (arg == "--dump-ir") {
    opts.dump_ir = true;
    return true;
  }
  if (arg == "-Wall") {
    opts.wall = true;
    return true;
  }
  if (arg == "-Werror") {
    opts.werror = true;
    return true;
  }
  return false;
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
  if (arg == "--area") {
    opts.area_mode = true;
    return true;
  }
  if (arg == "--delay") {
    opts.delay_mode = true;
    return true;
  }
  if (arg == "--retime") {
    opts.retime = true;
    return true;
  }
  return false;
}

bool TryParseLibArg(std::string_view arg, int& i, int argc,
                    const char* const argv[], CliOptions& opts) {
  ArgCursor cur{i, argc, argv, opts};
  if (TakeValue(arg, "-v", cur, opts.lib_files)) return true;
  if (TakeValue(arg, "-y", cur, opts.lib_dirs)) return true;
  if (TakeValue(arg, "-L", cur, opts.lib_search_order)) return true;
  if (TakeValue(arg, "--config", cur, opts.config)) return true;
  if (TakeValue(arg, "--load-lib", cur, opts.precompiled_libs)) return true;
  if (TakeValue(arg, "--precompile-into", cur, opts.precompile_library)) {
    return true;
  }
  return TakeValue(arg, "--precompile-out", cur, opts.precompile_output);
}

bool TryParseDefineArg(std::string_view arg, int& i, int argc,
                       const char* const argv[], CliOptions& opts) {
  if (arg.starts_with("-D") && arg.size() > 2) {
    ParseDefine(arg.substr(2), opts);
    return true;
  }
  if (arg != "-D") return false;
  if (i + 1 >= argc) {
    ReportMissingValue("-D", opts);
    return true;
  }
  ParseDefine(argv[++i], opts);
  return true;
}

bool TryParseSingleArg(std::string_view arg, int& i, int argc,
                       const char* const argv[], CliOptions& opts) {
  if (TryParseGeneralFlag(arg, opts)) return true;
  if (TryParseSynthFlag(arg, opts)) return true;
  if (TryParseDefineArg(arg, i, argc, argv, opts)) return true;
  if (TryParseSimArg(arg, i, argc, argv, opts)) return true;
  if (TryParseSynthArg(arg, i, argc, argv, opts)) return true;
  if (TryParseLibArg(arg, i, argc, argv, opts)) return true;
  if (delta::TryParseProtectArg(arg, i, argc, argv, opts.protect)) {
    // §34.3.1's options record a refused value on their own struct, which is
    // the one they are handed. Carrying it here is what makes ParseArgs fail
    // the parse for one, as it does for every other option group.
    if (opts.protect.rejected_argument) opts.rejected_argument = true;
    return true;
  }
  return false;
}

// How deep a `-f` may nest. An options file naming another is ordinary, and one
// naming itself recurses without bound; a limit refuses every cycle, including
// two files that name each other, where a set of the files already read would
// let a cycle of length two through unless it recorded the whole chain. The
// figure is a budget rather than a rule: nothing about a command line says how
// deep its options files may go, and sixteen is past any nesting a person
// writes.
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
  std::string word;
  while (ifs >> word) {
    if (!word.empty() && word[0] == '#') {
      std::string rest;
      std::getline(ifs, rest);
      continue;
    }
    words.push_back(std::move(word));
  }
  // ParseArgs reads from argv[1], so argv[0] is filled with the program name it
  // skips. The name is held in a buffer of its own rather than pointed at a
  // string literal, which would need casting away const to match char* argv[].
  std::string program = "deltahdl";
  std::vector<char*> ptrs;
  ptrs.push_back(program.data());
  for (auto& w : words) {
    ptrs.push_back(w.data());
  }
  return ParseArgsAtDepth(static_cast<int>(ptrs.size()), ptrs.data(), opts,
                          depth + 1);
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
  return false;
}

// Reads the options file `-f` names at `i`, and answers whether the parse may
// go on. A `-f` written last has no file to read, which is reported the way
// every other missing value is and leaves the parse to run to its end; a file
// that could not be read, or that nests too deep, stops it.
bool TakeOptionsFile(int& i, int argc, char* argv[], CliOptions& opts,
                     int depth) {
  if (i + 1 >= argc) {
    ReportMissingValue("-f", opts);
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
    if (arg.starts_with("-") || arg.starts_with("+")) {
      std::cerr << "unknown option: " << arg << "\n";
      return false;
    }
    opts.source_files.emplace_back(arg);
  }
  // A rejected argument fails the parse as an unrecognized option does, and
  // the loop runs to its end first so that the remaining arguments are still
  // checked. Nothing runs on this path: main returns 1 without preprocessing.
  return !opts.rejected_argument;
}

}  // namespace

bool ParseArgs(int argc, char* argv[], CliOptions& opts) {
  return ParseArgsAtDepth(argc, argv, opts, 0);
}

}  // namespace delta
