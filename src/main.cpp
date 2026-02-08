#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "simulation/scheduler.h"

namespace {

struct CliOptions {
  std::vector<std::string> source_files;
  std::string top_module;
  std::string vcd_file;
  std::string output_file;
  std::vector<std::string> include_dirs;
  std::vector<std::pair<std::string, std::string>> defines;
  uint64_t max_time = 0;
  uint32_t seed = 0;
  bool synth_mode = false;
  bool lint_only = false;
  bool dump_ast = false;
  bool dump_ir = false;
  bool wall = false;
  bool werror = false;
  bool show_version = false;
  bool show_help = false;
};

void print_version() {
  std::cout << "deltahdl 0.1.0\n";
  std::cout << "SystemVerilog IEEE 1800-2023 simulator and synthesizer\n";
}

void print_help() {
  print_version();
  std::cout << "\nUsage: deltahdl [options] <source-files...>\n\n"
            << "Options:\n"
            << "  -o <name>            Set output name\n"
            << "  --top <module>       Top-level module\n"
            << "  --vcd <file>         Dump VCD waveforms\n"
            << "  --max-time <time>    Maximum simulation time\n"
            << "  --seed <n>           Random seed\n"
            << "  --synth              Synthesis mode\n"
            << "  --lint-only          Parse and elaborate only\n"
            << "  +define+<n>=<v>      Define macro\n"
            << "  +incdir+<path>       Include directory\n"
            << "  -Wall -Werror        Warning controls\n"
            << "  --version / --help   Info\n";
}

void parse_define(std::string_view def, CliOptions& opts) {
  auto eq = def.find('=');
  if (eq == std::string_view::npos) {
    opts.defines.emplace_back(std::string(def), "1");
    return;
  }
  opts.defines.emplace_back(std::string(def.substr(0, eq)),
                            std::string(def.substr(eq + 1)));
}

bool try_parse_valued_arg(std::string_view arg, int& i, int argc, char* argv[],
                          CliOptions& opts) {
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
  if (arg == "--max-time" && i + 1 < argc) {
    opts.max_time = std::stoull(argv[++i]);
    return true;
  }
  if (arg == "--seed" && i + 1 < argc) {
    opts.seed = std::stoul(argv[++i]);
    return true;
  }
  return false;
}

bool try_parse_flag(std::string_view arg, CliOptions& opts) {
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

bool parse_args(int argc, char* argv[], CliOptions& opts) {
  for (int i = 1; i < argc; ++i) {
    std::string_view arg = argv[i];
    if (try_parse_flag(arg, opts)) {
      continue;
    }
    if (try_parse_valued_arg(arg, i, argc, argv, opts)) {
      continue;
    }
    if (arg.starts_with("+define+")) {
      parse_define(arg.substr(8), opts);
      continue;
    }
    if (arg.starts_with("+incdir+")) {
      opts.include_dirs.emplace_back(arg.substr(8));
      continue;
    }
    if (arg.starts_with("-")) {
      std::cerr << "unknown option: " << arg << "\n";
      return false;
    }
    opts.source_files.emplace_back(arg);
  }
  return true;
}

std::string read_file(const std::string& path) {
  std::ifstream ifs(path);
  if (!ifs) {
    std::cerr << "error: cannot open file '" << path << "'\n";
    return "";
  }
  std::ostringstream ss;
  ss << ifs.rdbuf();
  return ss.str();
}

std::string preprocess_sources(const CliOptions& opts,
                               delta::SourceManager& src_mgr,
                               delta::DiagEngine& diag) {
  delta::PreprocConfig pp_config;
  pp_config.include_dirs = opts.include_dirs;
  pp_config.defines = opts.defines;
  delta::Preprocessor preproc(src_mgr, diag, std::move(pp_config));

  std::string combined;
  for (const auto& path : opts.source_files) {
    auto content = read_file(path);
    if (content.empty()) {
      return "";
    }
    auto file_id = src_mgr.add_file(path, content);
    combined += preproc.preprocess(file_id);
  }
  return combined;
}

delta::CompilationUnit* parse_source(std::string& source,
                                     delta::SourceManager& src_mgr,
                                     delta::DiagEngine& diag,
                                     delta::Arena& arena) {
  auto file_id = src_mgr.add_file("<preprocessed>", source);
  delta::Lexer lexer(source, file_id, diag);
  delta::Parser parser(lexer, arena, diag);
  return parser.parse();
}

int run_simulation(const CliOptions& opts, delta::CompilationUnit* cu,
                   delta::DiagEngine& diag, delta::Arena& arena) {
  delta::Elaborator elaborator(arena, diag, cu);
  auto top = opts.top_module;
  if (top.empty() && !cu->modules.empty()) {
    top = std::string(cu->modules.back()->name);
  }
  auto* design = elaborator.elaborate(top);
  if (diag.has_errors() || design == nullptr) {
    return 1;
  }

  delta::Scheduler scheduler;
  scheduler.run();
  return diag.has_errors() ? 1 : 0;
}

}  // anonymous namespace

int main(int argc, char* argv[]) {
  CliOptions opts;
  if (!parse_args(argc, argv, opts)) {
    return 1;
  }
  if (opts.show_version) {
    print_version();
    return 0;
  }
  if (opts.show_help || opts.source_files.empty()) {
    print_help();
    return opts.show_help ? 0 : 1;
  }

  delta::SourceManager src_mgr;
  delta::DiagEngine diag(src_mgr);
  if (opts.werror) {
    diag.set_warnings_as_errors(true);
  }

  auto source = preprocess_sources(opts, src_mgr, diag);
  if (source.empty() || diag.has_errors()) {
    return 1;
  }

  delta::Arena ast_arena;
  auto* cu = parse_source(source, src_mgr, diag, ast_arena);
  if (diag.has_errors()) {
    return 1;
  }

  if (opts.lint_only) {
    std::cout << "lint pass: no errors\n";
    return 0;
  }

  delta::Arena elab_arena;
  return run_simulation(opts, cu, diag, elab_arena);
}
