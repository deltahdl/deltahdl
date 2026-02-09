#include <cstdlib>
#include <fstream>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/vcd_writer.h"
#include "synthesis/aig_opt.h"
#include "synthesis/synth_lower.h"

namespace {

struct CliOptions {
  std::vector<std::string> source_files;
  std::string top_module;
  std::string vcd_file;
  std::string output_file;
  std::string timescale;
  std::string fst_file;
  std::string format;
  std::string lib_file;
  std::string target;
  std::vector<std::string> include_dirs;
  std::vector<std::string> lib_dirs;
  std::vector<std::string> lib_files;
  std::vector<std::pair<std::string, std::string>> defines;
  uint64_t max_time = 0;
  uint32_t seed = 0;
  uint32_t lut_size = 4;
  bool synth_mode = false;
  bool lint_only = false;
  bool dump_ast = false;
  bool dump_ir = false;
  bool dump_aig = false;
  bool no_opt = false;
  bool area_mode = false;
  bool delay_mode = false;
  bool retime = false;
  bool wall = false;
  bool werror = false;
  bool show_version = false;
  bool show_help = false;
};

void PrintVersion() {
  std::cout << "deltahdl 0.1.0\n";
  std::cout << "SystemVerilog IEEE 1800-2023 simulator and synthesizer\n";
}

void PrintHelp() {
  PrintVersion();
  std::cout << "\nUsage: deltahdl [options] <source-files...>\n\n"
            << "General:\n"
            << "  -o <name>            Set output name\n"
            << "  --top <module>       Top-level module\n"
            << "  -f <file>            Read options from file\n"
            << "  -v <file>            Verilog library file\n"
            << "  -y <dir>             Verilog library directory\n"
            << "  +define+<n>=<v>      Define macro\n"
            << "  +incdir+<path>       Include directory\n"
            << "  -Wall -Werror        Warning controls\n"
            << "  --version / --help   Info\n\n"
            << "Simulation:\n"
            << "  --vcd <file>         Dump VCD waveforms\n"
            << "  --fst <file>         Dump FST waveforms\n"
            << "  --max-time <time>    Maximum simulation time\n"
            << "  --seed <n>           Random seed\n"
            << "  --timescale <t/p>    Override default timescale\n"
            << "  --lint-only          Parse and elaborate only\n"
            << "  --dump-ast           Print AST to stdout\n"
            << "  --dump-ir            Print RTLIR to stdout\n\n"
            << "Synthesis:\n"
            << "  --synth              Synthesis mode\n"
            << "  --target <name>      Target technology\n"
            << "  --lut-size <n>       LUT input count (default 4)\n"
            << "  --lib <file>         Liberty timing library\n"
            << "  --format <fmt>       Output format (blif/verilog/json/edif)\n"
            << "  --no-opt             Skip optimization passes\n"
            << "  --area               Area-oriented optimization\n"
            << "  --delay              Delay-oriented optimization\n"
            << "  --retime             Enable register retiming\n"
            << "  --dump-aig           Print AIG to stdout\n";
}

void ParseDefine(std::string_view def, CliOptions& opts) {
  auto eq = def.find('=');
  if (eq == std::string_view::npos) {
    opts.defines.emplace_back(std::string(def), "1");
    return;
  }
  opts.defines.emplace_back(std::string(def.substr(0, eq)),
                            std::string(def.substr(eq + 1)));
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
  if (arg == "--max-time" && i + 1 < argc) {
    opts.max_time = std::stoull(argv[++i]);
    return true;
  }
  if (arg == "--seed" && i + 1 < argc) {
    opts.seed = std::stoul(argv[++i]);
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
  return false;
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
  return false;
}

bool TryParseSingleArg(std::string_view arg, int& i, int argc,
                       const char* const argv[], CliOptions& opts) {
  if (TryParseGeneralFlag(arg, opts)) return true;
  if (TryParseSynthFlag(arg, opts)) return true;
  if (TryParseSimArg(arg, i, argc, argv, opts)) return true;
  if (TryParseSynthArg(arg, i, argc, argv, opts)) return true;
  if (TryParseLibArg(arg, i, argc, argv, opts)) return true;
  return false;
}

bool ParseArgs(int argc, char* argv[], CliOptions& opts);

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
  return true;
}

std::string ReadFile(const std::string& path) {
  std::ifstream ifs(path);
  if (!ifs) {
    std::cerr << "error: cannot open file '" << path << "'\n";
    return "";
  }
  std::ostringstream ss;
  ss << ifs.rdbuf();
  return ss.str();
}

std::string PreprocessSources(const CliOptions& opts,
                              delta::SourceManager& src_mgr,
                              delta::DiagEngine& diag) {
  delta::PreprocConfig pp_config;
  pp_config.include_dirs = opts.include_dirs;
  pp_config.defines = opts.defines;
  delta::Preprocessor preproc(src_mgr, diag, std::move(pp_config));

  std::string combined;
  for (const auto& path : opts.source_files) {
    auto content = ReadFile(path);
    if (content.empty()) {
      return "";
    }
    auto file_id = src_mgr.AddFile(path, content);
    combined += preproc.Preprocess(file_id);
  }
  return combined;
}

delta::CompilationUnit* ParseSource(const std::string& source,
                                    delta::SourceManager& src_mgr,
                                    delta::DiagEngine& diag,
                                    delta::Arena& arena) {
  auto file_id = src_mgr.AddFile("<preprocessed>", source);
  delta::Lexer lexer(source, file_id, diag);
  delta::Parser parser(lexer, arena, diag);
  return parser.Parse();
}

void SetupVcd(delta::VcdWriter& vcd, delta::SimContext& ctx,
              delta::Scheduler& scheduler, const std::string& top) {
  ctx.SetVcdWriter(&vcd);
  vcd.WriteHeader("1ns");
  vcd.BeginScope(top);
  for (const auto& [name, var] : ctx.GetVariables()) {
    vcd.RegisterSignal(name, var->value.width, var);
  }
  vcd.EndScope();
  vcd.EndDefinitions();
  vcd.WriteTimestamp(0);
  vcd.DumpAllValues();

  scheduler.SetPostTimestepCallback([&vcd, &ctx]() {
    vcd.WriteTimestamp(ctx.CurrentTime().ticks);
    vcd.DumpChangedValues(0);
  });
}

void DumpAst(const delta::CompilationUnit* cu) {
  std::cout << "=== AST Dump ===\n";
  for (const auto* mod : cu->modules) {
    std::cout << "module " << mod->name << ": " << mod->ports.size()
              << " ports, " << mod->items.size() << " items\n";
  }
  for (const auto* pkg : cu->packages) {
    std::cout << "package " << pkg->name << ": " << pkg->items.size()
              << " items\n";
  }
}

void DumpIr(const delta::RtlirDesign* design) {
  std::cout << "=== RTLIR Dump ===\n";
  for (const auto* mod : design->top_modules) {
    std::cout << "module " << mod->name << ": " << mod->ports.size()
              << " ports, " << mod->nets.size() << " nets, "
              << mod->variables.size() << " vars, " << mod->assigns.size()
              << " assigns, " << mod->processes.size() << " processes, "
              << mod->children.size() << " children\n";
  }
}

int RunSynthesis(const CliOptions& opts, delta::CompilationUnit* cu,
                 delta::DiagEngine& diag, delta::Arena& arena) {
  delta::Elaborator elaborator(arena, diag, cu);
  auto top = opts.top_module;
  if (top.empty() && !cu->modules.empty()) {
    top = std::string(cu->modules.back()->name);
  }
  const auto* design = elaborator.Elaborate(top);
  if (diag.HasErrors() || design == nullptr || design->top_modules.empty()) {
    return 1;
  }
  if (opts.dump_ir) DumpIr(design);

  delta::SynthLower synth(arena, diag);
  auto* aig = synth.Lower(design->top_modules[0]);
  if (!aig) return 1;

  if (!opts.no_opt) {
    delta::ConstProp(*aig);
    delta::Balance(*aig);
    delta::Rewrite(*aig);
  }

  if (opts.dump_aig) {
    std::cout << "AIG: " << aig->NodeCount() << " nodes, " << aig->inputs.size()
              << " inputs, " << aig->outputs.size() << " outputs, "
              << aig->latches.size() << " latches\n";
  }

  std::cout << "synthesis: " << aig->NodeCount() << " AIG nodes, "
            << aig->inputs.size() << " inputs, " << aig->outputs.size()
            << " outputs, " << aig->latches.size() << " latches\n";
  return 0;
}

int RunSimulation(const CliOptions& opts, delta::CompilationUnit* cu,
                  delta::DiagEngine& diag, delta::Arena& arena) {
  delta::Elaborator elaborator(arena, diag, cu);
  auto top = opts.top_module;
  if (top.empty() && !cu->modules.empty()) {
    top = std::string(cu->modules.back()->name);
  }
  const auto* design = elaborator.Elaborate(top);
  if (diag.HasErrors() || design == nullptr) {
    return 1;
  }
  if (opts.dump_ir) DumpIr(design);

  delta::Scheduler scheduler(arena);
  delta::SimContext sim_ctx(scheduler, arena, diag, opts.seed);
  delta::Lowerer lowerer(sim_ctx, arena, diag);
  lowerer.Lower(design);

  std::unique_ptr<delta::VcdWriter> vcd;
  if (!opts.vcd_file.empty()) {
    vcd = std::make_unique<delta::VcdWriter>(opts.vcd_file);
    SetupVcd(*vcd, sim_ctx, scheduler, top);
  }

  scheduler.Run();
  sim_ctx.RunFinalBlocks();
  return diag.HasErrors() ? 1 : 0;
}

}  // anonymous namespace

int main(int argc, char* argv[]) {
  CliOptions opts;
  if (!ParseArgs(argc, argv, opts)) {
    return 1;
  }
  if (opts.show_version) {
    PrintVersion();
    return 0;
  }
  if (opts.show_help || opts.source_files.empty()) {
    PrintHelp();
    return opts.show_help ? 0 : 1;
  }

  delta::SourceManager src_mgr;
  delta::DiagEngine diag(src_mgr);
  if (opts.werror) {
    diag.SetWarningsAsErrors(true);
  }

  auto source = PreprocessSources(opts, src_mgr, diag);
  if (source.empty() || diag.HasErrors()) {
    return 1;
  }

  delta::Arena ast_arena;
  auto* cu = ParseSource(source, src_mgr, diag, ast_arena);
  if (diag.HasErrors()) {
    return 1;
  }

  if (opts.dump_ast) {
    DumpAst(cu);
  }

  if (opts.lint_only) {
    std::cout << "lint pass: no errors\n";
    return 0;
  }

  delta::Arena elab_arena;
  if (opts.synth_mode) {
    return RunSynthesis(opts, cu, diag, elab_arena);
  }
  return RunSimulation(opts, cu, diag, elab_arena);
}
