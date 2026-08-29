#include "driver/cli_options.h"

#include <fstream>
#include <iostream>
#include <string>
#include <string_view>
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

// The simulation options whose argument is a number rather than a name, split
// out from TryParseSimArg below so that neither function's branch count grows
// with the other's. A caller reaches these through TryParseSimArg; the split is
// not visible on the command line.
bool TryParseSimNumericArg(std::string_view arg, int& i, int argc,
                           const char* const argv[], CliOptions& opts) {
  if (arg == "--max-time" && i + 1 < argc) {
    opts.max_time = std::stoull(argv[++i]);
    return true;
  }
  if (arg == "--seed" && i + 1 < argc) {
    opts.seed = std::stoul(argv[++i]);
    return true;
  }
  if (arg == "--max-generate-iterations" && i + 1 < argc) {
    opts.max_generate_iterations = std::stoll(argv[++i]);
    return true;
  }
  return false;
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
// already printed what is actually wrong with it.
bool TryParseMinTypMaxArg(std::string_view arg, int& i, int argc,
                          const char* const argv[], CliOptions& opts) {
  if (arg != "--mintypmax" || i + 1 >= argc) return false;
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
  if (arg == "--top" && i + 1 < argc) {
    opts.top_module = argv[++i];
    return true;
  }
  if (arg == "--vcd" && i + 1 < argc) {
    opts.vcd_file = argv[++i];
    return true;
  }
  if (arg == "-o" && i + 1 < argc) {
    opts.output_file = argv[++i];
    return true;
  }
  if (arg == "--timescale" && i + 1 < argc) {
    opts.timescale = argv[++i];
    return true;
  }
  if (arg == "--fst" && i + 1 < argc) {
    opts.fst_file = argv[++i];
    return true;
  }
  if (TryParseSimNumericArg(arg, i, argc, argv, opts)) return true;
  return TryParseMinTypMaxArg(arg, i, argc, argv, opts);
}

bool TryParseSynthArg(std::string_view arg, int& i, int argc,
                      const char* const argv[], CliOptions& opts) {
  if (arg == "--target" && i + 1 < argc) {
    opts.target = argv[++i];
    return true;
  }
  if (arg == "--lut-size" && i + 1 < argc) {
    opts.lut_size = std::stoul(argv[++i]);
    return true;
  }
  if (arg == "--lib" && i + 1 < argc) {
    opts.lib_file = argv[++i];
    return true;
  }
  if (arg == "--format" && i + 1 < argc) {
    opts.format = argv[++i];
    return true;
  }
  return false;
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
  if (arg == "-v" && i + 1 < argc) {
    opts.lib_files.emplace_back(argv[++i]);
    return true;
  }
  if (arg == "-y" && i + 1 < argc) {
    opts.lib_dirs.emplace_back(argv[++i]);
    return true;
  }

  if (arg == "-L" && i + 1 < argc) {
    opts.lib_search_order.emplace_back(argv[++i]);
    return true;
  }
  if (arg == "--config" && i + 1 < argc) {
    opts.config = argv[++i];
    return true;
  }
  if (arg == "--load-lib" && i + 1 < argc) {
    opts.precompiled_libs.emplace_back(argv[++i]);
    return true;
  }
  if (arg == "--precompile-into" && i + 1 < argc) {
    opts.precompile_library = argv[++i];
    return true;
  }
  if (arg == "--precompile-out" && i + 1 < argc) {
    opts.precompile_output = argv[++i];
    return true;
  }
  return false;
}

bool TryParseDefineArg(std::string_view arg, int& i, int argc,
                       const char* const argv[], CliOptions& opts) {
  if (arg.starts_with("-D") && arg.size() > 2) {
    ParseDefine(arg.substr(2), opts);
    return true;
  }
  if (arg == "-D" && i + 1 < argc) {
    ParseDefine(argv[++i], opts);
    return true;
  }
  return false;
}

bool TryParseSingleArg(std::string_view arg, int& i, int argc,
                       const char* const argv[], CliOptions& opts) {
  if (TryParseGeneralFlag(arg, opts)) return true;
  if (TryParseSynthFlag(arg, opts)) return true;
  if (TryParseDefineArg(arg, i, argc, argv, opts)) return true;
  if (TryParseSimArg(arg, i, argc, argv, opts)) return true;
  if (TryParseSynthArg(arg, i, argc, argv, opts)) return true;
  if (TryParseLibArg(arg, i, argc, argv, opts)) return true;
  if (delta::TryParseProtectArg(arg, i, argc, argv, opts.protect)) return true;
  return false;
}

bool ReadOptionsFile(const std::string& path, CliOptions& opts) {
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
  std::vector<char*> ptrs;
  ptrs.push_back(const_cast<char*>("deltahdl"));
  for (auto& w : words) {
    ptrs.push_back(w.data());
  }
  return ParseArgs(static_cast<int>(ptrs.size()), ptrs.data(), opts);
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

}  // namespace

bool ParseArgs(int argc, char* argv[], CliOptions& opts) {
  for (int i = 1; i < argc; ++i) {
    std::string_view arg = argv[i];
    if (TryParseSingleArg(arg, i, argc, argv, opts)) continue;
    if (TryParsePlusArg(arg, opts)) continue;
    if (arg == "-f" && i + 1 < argc) {
      if (!ReadOptionsFile(argv[++i], opts)) return false;
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

}  // namespace delta
