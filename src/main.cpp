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
#include "common/types.h"
#include "driver/cli_options.h"
#include "elaborator/command_line_bind.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/separate_compilation_bind.h"
#include "lexer/lexer.h"
#include "parser/library_map.h"
#include "parser/parser.h"
#include "parser/precompiled_library.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_cli.h"
#include "preprocessor/protect_processing.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "synthesizer/aig_opt.h"
#include "synthesizer/synth_lower.h"

namespace {

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
            << "  --mintypmax <val>    min:typ:max member: min, typ or max\n"
            << "  --max-generate-iterations <n>\n"
            << "                       Loop generate iteration budget "
               "(default 262144)\n"
            << "  -f <file>            Read options from file\n"
            << "  -v <file>            Verilog library file\n"
            << "  -y <dir>             Verilog library directory\n"
            << "  -L <name>            Library search order (repeatable)\n"
            << "  +define+<n>=<v>      Define macro\n"
            << "  +incdir+<path>       Include directory\n"
            << "  -Wall -Werror        Warning controls\n"
            << "  --version / --help   Info\n\n"
            << "Protected envelopes:\n"
            << "  --encrypt            Encrypt the `pragma protect envelopes "
               "and write the text\n"
            << "  --protect-key <key>  Key every region is encrypted under\n"
            << "  --protect-named-key <owner>:<name>=<key>\n"
            << "                       Key selecting the regions naming it "
               "(repeatable)\n\n"
            << "Simulation:\n"
            << "  --vcd <file>         Dump VCD waveforms\n"
            << "  --fst <file>         Dump FST waveforms\n"
            << "  --max-time <time>    Maximum simulation time\n"
            << "  --seed <n>           Random seed\n"
            << "  --timescale <t/p>    Override default timescale\n"
            << "  -D <name>[=<value>]  Define preprocessor macro\n"
            << "  --lint-only          Parse and elaborate only\n"
            << "  --dump-ast           Print AST to stdout\n"
            << "  --dump-ir            Print RTLIR to stdout\n\n"
            << "Synthesis:\n"
            << "  --synth              Synthesis mode\n"
            << "  --target <name>      Target technology\n"
            << "  --lut-size <n>       LUT input count (default 4)\n"
            << "  --lib <file>         Liberty timing library\n"
            << "  --config <name>      Configuration to bind (33.5.4)\n"
            << "  --load-lib <file>    Precompiled library to bind from\n"
            << "  --precompile-into <library>\n"
            << "                       Library to compile sources into\n"
            << "  --precompile-out <file>\n"
            << "                       File the precompiled cells go to\n"
            << "  --format <fmt>       Output format (blif/verilog/json/edif)\n"
            << "  --no-opt             Skip optimization passes\n"
            << "  --area               Area-oriented optimization\n"
            << "  --delay              Delay-oriented optimization\n"
            << "  --retime             Enable register retiming\n"
            << "  --dump-aig           Print AIG to stdout\n";
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

struct PreprocResult {
  std::string source;
  // The source each line of `source` was written on, which §22.12 requires a
  // compiler to maintain and which `source` does not carry: it splices in the
  // lines of every `include and joins a `define body that spanned continuation
  // lines. It travels beside `source` because the two are appended together.
  std::vector<delta::OutputLineOrigin> line_origins;
  delta::NetType default_nettype = delta::NetType::kWire;
  delta::NetType unconnected_drive = delta::NetType::kWire;
  std::vector<std::string> cell_module_names;

  uint64_t default_decay_time = 0;
  double default_decay_time_real = 0.0;
  bool default_decay_time_infinite = true;

  uint32_t default_trireg_strength = 0;
  bool has_default_trireg_strength = false;

  delta::DelayModeDirective delay_mode_directive =
      delta::DelayModeDirective::kNone;

  delta::TimeScale timescale;
  bool has_timescale = false;
};

PreprocResult PreprocessSources(const delta::CliOptions& opts,
                                delta::SourceManager& src_mgr,
                                delta::DiagEngine& diag) {
  delta::PreprocConfig pp_config;
  pp_config.include_dirs = opts.include_dirs;
  pp_config.defines = opts.defines;
  delta::Preprocessor preproc(src_mgr, diag, std::move(pp_config));

  PreprocResult result;
  for (const auto& path : opts.source_files) {
    auto content = ReadFile(path);
    if (content.empty()) {
      return result;
    }
    auto file_id = src_mgr.AddFile(path, content);
    result.source += preproc.Preprocess(file_id);
  }
  // A `begin_keywords region may span source file boundaries (22.14), so the
  // pairing check only makes sense once every file has been preprocessed.
  preproc.ReportUnterminatedKeywordRegions();
  result.line_origins = preproc.LineOrigins();
  result.default_nettype = preproc.DefaultNetType();
  result.unconnected_drive = preproc.UnconnectedDrive();
  result.cell_module_names = preproc.CellModuleNames();
  result.default_decay_time = preproc.DefaultDecayTime();
  result.default_decay_time_real = preproc.DefaultDecayTimeReal();
  result.default_decay_time_infinite = preproc.DefaultDecayTimeInfinite();
  result.default_trireg_strength = preproc.DefaultTriregStrength();
  result.has_default_trireg_strength = preproc.HasDefaultTriregStrength();
  result.delay_mode_directive = preproc.DelayModeDirective();
  result.timescale = preproc.CurrentTimescale();
  result.has_timescale = preproc.HasTimescale();
  return result;
}

delta::CompilationUnit* ParseSource(
    const std::string& source,
    const std::vector<delta::OutputLineOrigin>& line_origins,
    delta::SourceManager& src_mgr, delta::DiagEngine& diag,
    delta::Arena& arena) {
  // Registered with its origins, so a report about a token of this text names
  // the file and line somebody can open rather than a position in a buffer
  // they have never seen. The path stays <preprocessed> because it is what a
  // position with no origin recorded falls back to.
  auto file_id =
      src_mgr.AddPreprocessedFile("<preprocessed>", source, line_origins);
  delta::Lexer lexer(source, file_id, diag,
                     delta::TextOrigin::kPreprocessorOutput);
  delta::Parser parser(lexer, arena, diag);
  return parser.Parse();
}

// --vcd is not one of the VCD system tasks §21.7.1 creates a dump file with,
// so it opens the same dump those tasks open -- SimContext::OpenVcdDump writes
// the header, the definitions and the per-timestep recording either way. What
// differs is that no $dumpvars is coming to start this one (§21.7.1.3): the
// option asks for the whole design dumped from time 0, so the recording is not
// held back.
//
// The option runs before the scheduler does, so its writer is the one in place
// when a source that also calls the VCD tasks reaches its first $dumpfile.
// That call finds the dump already open and adds nothing; the file named on
// the command line is the one written.
void SetupVcd(delta::SimContext& ctx, const std::string& top,
              const std::string& vcd_file) {
  ctx.SetDumpFileName(vcd_file);
  // Reproduce the $dumpfile call that would have named this output in the
  // $version section (§21.7.2.3).
  ctx.SetDumpFileLiteral("\"" + vcd_file + "\"");
  // §21.7.1: the option stands in for the tasks that create the 4-state file,
  // so that is the type it opens. §21.7.3.1 gives $dumpports a file of its own,
  // so a source calling it afterwards writes its extended dump beside this one
  // rather than into it.
  ctx.OpenVcdDump(top, /*wait_for_dumpvars=*/false,
                  delta::VcdFileType::kFourState);
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

void ApplyPreprocMetadata(delta::CompilationUnit* cu, const PreprocResult& pp) {
  cu->default_nettype = pp.default_nettype;
  cu->unconnected_drive = pp.unconnected_drive;
  delta::MarkCellModules(cu, pp.cell_module_names);
  cu->default_decay_time = pp.default_decay_time;
  cu->default_decay_time_real = pp.default_decay_time_real;
  cu->default_decay_time_infinite = pp.default_decay_time_infinite;
  cu->default_trireg_strength = pp.default_trireg_strength;
  cu->has_default_trireg_strength = pp.has_default_trireg_strength;
  cu->delay_mode_directive = pp.delay_mode_directive;
  cu->preproc_timescale = pp.timescale;
  cu->has_preproc_timescale = pp.has_timescale;
}

std::string ResolveTopModule(const delta::CliOptions& opts,
                             delta::CompilationUnit* cu) {
  if (!opts.top_module.empty()) return opts.top_module;
  if (!cu->modules.empty()) return std::string(cu->modules.back()->name);
  return "";
}

// §33.8.1: installs the library search order this invocation is to use, which
// the -L arguments override the library map's declaration order with. Those
// arguments carry library names and nothing else, so an argument that is not a
// library name names no library the map could define and the run stops instead
// of searching an order that was never asked for. Returns false in that case.
bool InstallLibrarySearchOrder(const delta::CliOptions& opts,
                               const delta::LibraryMap& lib_map,
                               delta::Elaborator& elaborator) {
  std::vector<std::string> errors;
  auto effective_order =
      lib_map.ResolveSearchOrder(opts.lib_search_order, &errors);
  for (const auto& err : errors) std::cerr << "error: " << err << "\n";
  if (!errors.empty()) return false;
  if (!effective_order.empty()) {
    elaborator.SetLibraryDeclarationOrder(std::move(effective_order));
  }
  return true;
}

const delta::RtlirDesign* ElaborateDesign(const delta::CliOptions& opts,
                                          delta::CompilationUnit* cu,
                                          delta::DiagEngine& diag,
                                          delta::Arena& arena) {
  // §11.11's three values are chosen among while a constant expression is
  // folded, and elaboration is where that folding happens, so the guard is
  // constructed here rather than in main: ElaborateDesign is the whole of the
  // elaboration, and both RunSimulation and RunSynthesis reach it through here.
  delta::DelayModeGuard mintypmax_guard(opts.mintypmax);

  delta::Elaborator elaborator(arena, diag, cu);
  elaborator.SetMaxGenerateIterations(opts.max_generate_iterations);

  delta::LibraryMap lib_map;
  if (!InstallLibrarySearchOrder(opts, lib_map, elaborator)) return nullptr;
  // §33.5.4: a configuration whose source description was named on the command
  // line settles the design, so the top-level cell named here is what a command
  // line that put no configuration in force is elaborated from.
  auto top = ResolveTopModule(opts, cu);
  const auto* design =
      delta::ElaborateCommandLine(elaborator, *cu, top, opts.config, diag);
  if (diag.HasErrors() || design == nullptr) return nullptr;
  if (opts.dump_ir) DumpIr(design);
  return design;
}

int RunSynthesis(const delta::CliOptions& opts, delta::CompilationUnit* cu,
                 delta::DiagEngine& diag, delta::Arena& arena) {
  const auto* design = ElaborateDesign(opts, cu, diag, arena);
  if (!design || design->top_modules.empty()) return 1;

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

int RunSimulation(const delta::CliOptions& opts, delta::CompilationUnit* cu,
                  delta::DiagEngine& diag, delta::Arena& arena) {
  const auto* design = ElaborateDesign(opts, cu, diag, arena);
  if (!design) return 1;
  auto top = ResolveTopModule(opts, cu);

  delta::Scheduler scheduler(arena);
  delta::SimContext sim_ctx(scheduler, arena, diag, opts.seed);
  // §11.11: the run selects the same member of a min:typ:max expression that
  // ElaborateDesign folded parameters at, which EvalMinTypMax in
  // src/simulator/evaluation.cpp reads back through SimContext::GetDelayMode.
  // It is set before the design is lowered so that a delay evaluated during
  // lowering sees it.
  sim_ctx.SetDelayMode(opts.mintypmax);
  delta::Lowerer lowerer(sim_ctx, arena, diag);
  lowerer.Lower(design);

  if (!opts.vcd_file.empty()) SetupVcd(sim_ctx, top, opts.vcd_file);

  scheduler.Run();
  sim_ctx.RunFinalBlocks();
  // §21.7.3.6.1: close the dump by recording the final simulation time, which
  // an extended VCD file ends with. This covers a dump the source's own VCD
  // tasks opened as well as one --vcd asked for, and does nothing when the run
  // opened none.
  sim_ctx.CloseVcdDump();
  return diag.HasErrors() ? 1 : 0;
}

}  // namespace

// §34.3.1's encrypting mode over the sources named on the command line: each
// text's encryption envelopes come back decryption envelopes, and everything
// outside them comes back as it was written. The produced text goes to standard
// output, one source after another, which is what lets an author redirect it
// into the file they mean to ship.
//
// The engine the run already holds is handed to EncryptEnvelopes, so the four
// conditions §34.5.1, §34.5.15 and §34.5.27 make an error in an input file are
// printed and decide the status. The transformation reads each text to its end
// whatever it found, so a breach costs the report rather than the text, and the
// text is still written; the status is what says it was not clean.
int RunEnvelopeEncryption(const delta::CliOptions& opts,
                          delta::SourceManager& src_mgr,
                          delta::DiagEngine& diag) {
  for (const auto& path : opts.source_files) {
    auto content = ReadFile(path);
    if (content.empty()) return 1;
    auto file_id = src_mgr.AddFile(path, content);
    std::cout << delta::EncryptEnvelopes(content, opts.protect.exchange_key,
                                         opts.protect.keys, &diag, file_id);
  }
  return diag.HasErrors() ? 1 : 0;
}

// §33.5.3's separate compilation tool: the invocation that compiles source
// descriptions into a library rather than binding a design. "It is essential
// that library cells persist, and the compiled forms shall, therefore, exist
// somewhere in the filesystem", which is what --precompile-out names and what a
// later --load-lib reads.
//
// Both options are required together. A library name with nowhere to write it
// leaves nothing that persists, and a file with no library name holds cells
// belonging to no library, which §33.5.3 has a bind select from.
int RunPrecompile(const delta::CliOptions& opts, delta::DiagEngine& diag) {
  if (opts.precompile_library.empty() || opts.precompile_output.empty()) {
    std::cerr << "--precompile-into and --precompile-out are used together\n";
    return 1;
  }
  for (const auto& path : opts.source_files) {
    auto content = ReadFile(path);
    if (content.empty()) return 1;
    if (!delta::PrecompiledLibrary::Save(content, opts.precompile_library,
                                         opts.precompile_output)) {
      std::cerr << "could not precompile " << path << " into "
                << opts.precompile_output << "\n";
      return 1;
    }
  }
  return diag.HasErrors() ? 1 : 0;
}

// §33.5.4's binding invocation: "the tool that actually does the binding only
// needs to be given the lib.cell specification for the top-level cell(s) and/or
// the config to be used. In this strategy, the config itself shall also be
// precompiled."
//
// So the cells come from the libraries --load-lib names and from nowhere else,
// and what roots the design is either --config or the top-level cells --top
// names. A configuration is looked for among the precompiled cells for the same
// reason every other cell is: this invocation reads no source description.
int RunSeparateCompilationBind(const delta::CliOptions& opts,
                               delta::SourceManager& src_mgr,
                               delta::DiagEngine& diag) {
  delta::Arena arena;
  delta::SeparateCompilationBinder binder(src_mgr, arena, diag);
  for (const auto& path : opts.precompiled_libs) {
    if (!binder.LoadLibrary(path)) return 1;
  }

  const delta::RtlirDesign* design = nullptr;
  if (!opts.config.empty()) {
    design = binder.BindConfig(opts.config);
  } else if (!opts.top_module.empty()) {
    design = binder.Bind({opts.top_module});
  } else {
    std::cerr << "a separate compilation bind names --config or --top\n";
    return 1;
  }
  if (design == nullptr || diag.HasErrors()) return 1;
  if (opts.dump_ir) DumpIr(design);
  return 0;
}

// The invocations that finish without elaborating a design out of the source
// descriptions named on the command line, each selected by an option of its
// own: §34.3.1's encrypting mode, §33.5.3's precompile into a library, and
// §33.5.4's bind from precompiled libraries. Returns true when one of them ran,
// leaving its status in `status`, which is meaningless otherwise.
//
// They are asked about together so that main states once that an invocation is
// either one of these or an ordinary elaboration, rather than once per mode.
bool RanStandaloneMode(const delta::CliOptions& opts,
                       delta::SourceManager& src_mgr, delta::DiagEngine& diag,
                       int& status) {
  if (opts.protect.encrypt) {
    status = RunEnvelopeEncryption(opts, src_mgr, diag);
    return true;
  }
  if (!opts.precompile_library.empty() || !opts.precompile_output.empty()) {
    status = RunPrecompile(opts, diag);
    return true;
  }
  if (!opts.precompiled_libs.empty()) {
    status = RunSeparateCompilationBind(opts, src_mgr, diag);
    return true;
  }
  return false;
}

int main(int argc, char* argv[]) {
  delta::CliOptions opts;
  if (!delta::ParseArgs(argc, argv, opts)) {
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

  int mode_status = 0;
  if (RanStandaloneMode(opts, src_mgr, diag, mode_status)) return mode_status;

  auto pp = PreprocessSources(opts, src_mgr, diag);
  if (pp.source.empty() || diag.HasErrors()) {
    return 1;
  }

  delta::Arena ast_arena;
  auto* cu = ParseSource(pp.source, pp.line_origins, src_mgr, diag, ast_arena);
  if (diag.HasErrors()) {
    return 1;
  }
  ApplyPreprocMetadata(cu, pp);

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
