#include <pthread.h>
// glibc declares pthread_t and pthread_attr_t in <bits/pthreadtypes.h>, which
// <pthread.h> reaches through <sys/types.h>; misc-include-cleaner asks for the
// header that declares a name and names no public one for these two, so the
// declaring header is included where it exists. Apple's SDK declares them in
// <pthread.h>'s own tree and has no such file.
#if __has_include(<bits/pthreadtypes.h>)
#include <bits/pthreadtypes.h>
#endif

#include <algorithm>
#include <charconv>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iostream>
#include <iterator>
#include <optional>
#include <sstream>
#include <string>
#include <string_view>
#include <system_error>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "driver/cli_options.h"
#include "driver/precompile_run.h"
#include "driver/protect_license_libraries.h"
#include "elaborator/command_line_bind.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/separate_compilation_bind.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/library_map.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_cli.h"
#include "preprocessor/protect_processing.h"
#include "simulator/cover_results.h"
#include "simulator/dpi_binding.h"
#include "simulator/foreign_code.h"
#include "simulator/lowerer.h"
#include "simulator/output_log.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/vcd_writer.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_user.h"
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
            << "  <file>.map           Library map file, read before the "
               "sources (33.3.1);\n"
            << "                       lib.map in the working directory "
               "when none is named\n"
            << "  +define+<n>=<v>      Define macro\n"
            << "  +incdir+<path>       Include directory\n"
            << "  +<plusarg>           Plusarg for $test$plusargs and "
               "$value$plusargs (21.6)\n"
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
            << "  --vpi-compat-mode <mode>\n"
            << "                       Default VPI compatibility mode "
               "(36.12.2.2):\n"
            << "                       1364v1995, 1364v2001, 1364v2005, "
               "1800v2005, 1800v2009\n"
            << "  --negative-timing-checks\n"
            << "                       Accept negative $setuphold/$recrem "
               "limits (31.9.4)\n"
            << "  --no-timing-checks   Turn every timing check off (31.9.4)\n"
            << "  -D <name>[=<value>]  Define preprocessor macro\n"
            << "  --lint-only          Parse and elaborate only\n"
            << "  --parse-only         Parse only\n"
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

struct PreprocResult {
  std::string source;
  // Whether a source file named on the command line could not be opened. Such
  // a file fails the run wherever it stands in the list, and empty text cannot
  // say so: a source of no bytes preprocesses to empty text too, and the text
  // gathered before a later file failed is not empty.
  bool unreadable = false;
  // The source each line of `source` was written on, which §22.12 requires a
  // compiler to maintain and which `source` does not carry: it splices in the
  // lines of every `include and joins a `define body that spanned continuation
  // lines. It travels beside `source` because the two are appended together.
  std::vector<delta::OutputLineOrigin> line_origins;
  delta::NetType default_nettype = delta::NetType::kWire;
  delta::NetType unconnected_drive = delta::NetType::kWire;
  std::vector<std::string> cell_module_names;
  std::vector<delta::ModuleDirectives> module_directives;

  uint64_t default_decay_time = 0;
  double default_decay_time_real = 0.0;
  bool default_decay_time_infinite = true;

  uint32_t default_trireg_strength = 0;
  bool has_default_trireg_strength = false;

  delta::DelayModeDirective delay_mode_directive =
      delta::DelayModeDirective::kNone;

  delta::TimeScale timescale;
  bool has_timescale = false;
  delta::TimeUnit global_precision = delta::TimeUnit::kNs;
  // The line of `source` each command-line source file's text begins on, in
  // command-line order. §33.3.1 maps a source file to a library, and a design
  // element belongs to the file named on the command line whose text holds
  // it, whichever file an `include put the element's own lines in.
  std::vector<std::pair<uint32_t, std::string>> file_first_lines;
  // The runtime_license expressions met in encrypted models, which §34.5.29.2
  // has asked before the model is executed.
  std::vector<delta::ProtectRuntimeLicense> runtime_licenses;
};

PreprocResult PreprocessSources(const delta::CliOptions& opts,
                                delta::SourceManager& src_mgr,
                                delta::DiagEngine& diag,
                                delta::ProtectLicenseLibraries& licenses) {
  delta::Preprocessor preproc(src_mgr, diag,
                              delta::PreprocConfigFor(opts, licenses.Asker()));

  PreprocResult result;
  for (const auto& path : opts.source_files) {
    std::optional<std::string> content = delta::ReadSource(path);
    if (!content) {
      result.unreadable = true;
      return result;
    }
    auto file_id = src_mgr.AddFile(path, std::move(*content));
    auto first_line = static_cast<uint32_t>(
        std::count(result.source.begin(), result.source.end(), '\n') + 1);
    result.file_first_lines.emplace_back(first_line, path);
    result.source += preproc.Preprocess(file_id);
  }
  // A `begin_keywords region may span source file boundaries (22.14), so the
  // pairing check only makes sense once every file has been preprocessed.
  preproc.ReportUnterminatedKeywordRegions();
  result.line_origins = preproc.LineOrigins();
  result.default_nettype = preproc.DefaultNetType();
  result.unconnected_drive = preproc.UnconnectedDrive();
  result.cell_module_names = preproc.CellModuleNames();
  result.module_directives = preproc.ModuleDirectivesList();
  result.default_decay_time = preproc.DefaultDecayTime();
  result.default_decay_time_real = preproc.DefaultDecayTimeReal();
  result.default_decay_time_infinite = preproc.DefaultDecayTimeInfinite();
  result.default_trireg_strength = preproc.DefaultTriregStrength();
  result.has_default_trireg_strength = preproc.HasDefaultTriregStrength();
  result.delay_mode_directive = preproc.DelayModeDirective();
  result.timescale = preproc.CurrentTimescale();
  result.has_timescale = preproc.HasTimescale();
  result.global_precision = preproc.GlobalPrecision();
  result.runtime_licenses = preproc.RuntimeLicenses();
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
  ctx.Vcd().SetDumpFileName(vcd_file);
  // Reproduce the $dumpfile call that would have named this output in the
  // $version section (§21.7.2.3).
  ctx.Vcd().SetDumpFileLiteral("\"" + vcd_file + "\"");
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
  delta::ApplyModuleDirectives(cu, pp.module_directives);
  cu->default_decay_time = pp.default_decay_time;
  cu->default_decay_time_real = pp.default_decay_time_real;
  cu->default_decay_time_infinite = pp.default_decay_time_infinite;
  cu->default_trireg_strength = pp.default_trireg_strength;
  cu->has_default_trireg_strength = pp.has_default_trireg_strength;
  cu->delay_mode_directive = pp.delay_mode_directive;
  cu->preproc_timescale = pp.timescale;
  cu->has_preproc_timescale = pp.has_timescale;
  cu->preproc_global_precision = pp.global_precision;
}

// §33.3.1 (printed pages 935-936): the library mapping is read from a
// predefined file before any source description is, and a tool lets an
// invocation name library map files of its own, which are then read in the
// order they were named. The predefined file is lib.map in the working
// directory, read where the command line names no map file of its own. False
// where a map file could not be read or parsed.
bool LoadLibraryMaps(const delta::CliOptions& opts,
                     delta::SourceManager& src_mgr,
                     delta::LibraryMap& lib_map) {
  lib_map.ResolvePositionsAgainst(src_mgr);
  std::vector<std::string> map_files = opts.library_map_files;
  std::error_code ec;
  if (map_files.empty() && std::filesystem::is_regular_file("lib.map", ec)) {
    map_files.emplace_back("lib.map");
  }
  for (const auto& map_file : map_files) {
    std::vector<std::string> errors;
    bool loaded = lib_map.LoadMapFile(map_file, &errors);
    for (const auto& err : errors) std::cerr << "error: " << err << "\n";
    // LibraryMap::LoadMapFile returns false on every path that records an
    // error, so `loaded` alone says whether the file was read.
    if (!loaded) return false;
  }
  return true;
}

// The command-line source file whose text holds line `line` of the
// preprocessed source.
std::string_view SourceFileHoldingLine(const PreprocResult& pp, uint32_t line) {
  std::string_view path;
  for (const auto& [first_line, file] : pp.file_first_lines) {
    if (first_line > line) break;
    path = file;
  }
  return path;
}

// §33.3.1 (printed page 936): a file that no library's file_path_spec matches
// is compiled into the default library, work, and a file that does match
// compiles into the library
// whose specification claims it, so every design element carries the library
// of the command-line file it was written in. A file several libraries claim
// equally belongs to none of them, which §33.3.1.1 makes an error.
bool TagDesignElementLibraries(delta::CompilationUnit& cu,
                               const PreprocResult& pp,
                               const delta::LibraryMap& lib_map,
                               delta::DiagEngine& diag) {
  bool ok = true;
  auto library_of = [&](delta::SourceLoc loc) -> std::string_view {
    std::string_view file = SourceFileHoldingLine(pp, loc.line);
    std::error_code ec;
    auto path = std::filesystem::weakly_canonical(
        std::filesystem::absolute(std::filesystem::path(file), ec), ec);
    std::string canonical = path.string();
    std::string_view library = lib_map.LibraryForFile(canonical);
    if (!library.empty()) return library;
    std::string claimants;
    for (auto name : lib_map.LibrariesForFile(canonical)) {
      if (!claimants.empty()) claimants += ", ";
      claimants += name;
    }
    diag.Error(lib_map.FirstDeclarationClaiming(canonical),
               "source description claimed by more than one library (" +
                   claimants + "): " + std::string(file),
               delta::Subclause("33.3.1.1"));
    ok = false;
    return library;
  };
  auto tag = [&](const auto& elements) {
    for (auto* element : elements) {
      element->library = library_of(element->range.start);
    }
  };
  tag(cu.modules);
  tag(cu.interfaces);
  tag(cu.programs);
  tag(cu.checkers);
  tag(cu.udps);
  tag(cu.packages);
  tag(cu.configs);
  return ok;
}

// The top-level instance a dump named on the command line is rooted at: the
// one --top names, else the first the design roots.
std::string DumpTopModule(const delta::CliOptions& opts,
                          const delta::RtlirDesign* design) {
  if (!opts.top_module.empty()) return opts.top_module;
  if (design->top_modules.empty()) return "";
  return std::string(design->top_modules.front()->name);
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

// What ElaborateDesign answers. A run that stopped on an error it reported has
// failed, whatever the source declares. A run that did not, and still has no
// design, came from a source that declares nothing -- a file of compiler
// directives, of comments alone or of no bytes at all, which Annex A.1.2 makes
// valid source text -- and has nothing to run.
struct Elaboration {
  const delta::RtlirDesign* design = nullptr;
  bool failed = false;
};

Elaboration ElaborateDesign(const delta::CliOptions& opts,
                            const delta::LibraryMap& lib_map,
                            delta::CompilationUnit* cu, delta::DiagEngine& diag,
                            delta::Arena& arena) {
  // §11.11's three values are chosen among while a constant expression is
  // folded, and elaboration is where that folding happens, so the guard is
  // constructed here rather than in main: ElaborateDesign is the whole of the
  // elaboration, and both RunSimulation and RunSynthesis reach it through here.
  delta::DelayModeGuard mintypmax_guard(opts.mintypmax);

  delta::Elaborator elaborator(arena, diag, cu);
  elaborator.SetMaxGenerateIterations(opts.max_generate_iterations);

  if (!InstallLibrarySearchOrder(opts, lib_map, elaborator)) {
    return {.failed = true};
  }
  // §33.5.4: a configuration whose source description was named on the command
  // line settles the design, so the top-level cell named here is what a command
  // line that put no configuration in force is elaborated from.
  //
  // §23.3.1 (printed page 740): a top-level module is one the source text
  // holds that no module instantiation statement names, so with no --top the
  // design is rooted at every such module, which ElaborateCommandLine collects
  // for an empty name. The last module in the source was taken for the top
  // instead, and a design whose top came before the modules it instantiates --
  // the standard's own §23.5 example, `module top` followed by `module m (.*)`
  // and `module a (.*)` -- elaborated one of those alone and ran nothing.
  const auto* design = delta::ElaborateCommandLine(
      elaborator, *cu, opts.top_module, opts.config, diag);
  if (diag.HasErrors()) return {.failed = true};
  if (design == nullptr) return {.failed = !cu->DeclaresNothing()};
  if (opts.dump_ir) DumpIr(design);
  return {.design = design};
}

// --synth lowers the design's first top-level module. A design with none, which
// is what a source declaring nothing or only packages, types or classes
// elaborates to, leaves nothing to lower, and the run says so rather than
// failing without a word. A run ElaborateDesign stopped on an error it
// reported adds nothing to that report. This is a limit of what synthesis can
// produce, not a rule of IEEE 1800-2023, so the report cites no subclause.
int RunSynthesis(const delta::CliOptions& opts,
                 const delta::LibraryMap& lib_map, delta::CompilationUnit* cu,
                 delta::DiagEngine& diag, delta::Arena& arena) {
  auto [design, failed] = ElaborateDesign(opts, lib_map, cu, diag, arena);
  if (failed) return 1;
  if (design == nullptr || design->top_modules.empty()) {
    std::cerr << "error: design has no top-level module to synthesize\n";
    return 1;
  }

  delta::SynthLower synth(arena, diag);
  auto* aig = synth.Lower(design->top_modules[0]);
  if (!aig) return 1;

  if (!opts.no_opt) {
    delta::ConstProp(*aig);
    delta::Balance(*aig);
    delta::Rewrite(*aig);
  }

  if (opts.dump_aig) {
    std::cout << "AIG: " << aig->ReachableNodeCount() << " nodes, "
              << aig->inputs.size() << " inputs, " << aig->outputs.size()
              << " outputs, " << aig->latches.size() << " latches\n";
  }

  std::cout << "synthesis: " << aig->ReachableNodeCount() << " AIG nodes, "
            << aig->inputs.size() << " inputs, " << aig->outputs.size()
            << " outputs, " << aig->latches.size() << " latches\n";
  return 0;
}

// --lint-only, "Parse and elaborate only": the design is elaborated as it is
// ahead of a simulation, so every rule the elaborator enforces is applied and
// reported, and nothing is run. The status is 1 on any report, including one
// ElaborateDesign writes on its own, such as an -L entry that is not a library
// name. A source that declares nothing, which is what a file of compiler
// directives, of comments alone or of no bytes at all is, has nothing to
// elaborate and nothing to report, and passes. Until this the option returned 0
// as soon as the source had parsed, so a source only the elaborator could
// reject was reported clean.
int RunLint(const delta::CliOptions& opts, const delta::LibraryMap& lib_map,
            delta::CompilationUnit* cu, delta::DiagEngine& diag,
            delta::Arena& arena) {
  if (ElaborateDesign(opts, lib_map, cu, diag, arena).failed) return 1;
  std::cout << "lint pass: no errors\n";
  return 0;
}

// Runs an elaborated design to its end: lowered into a simulation context,
// scheduled, and its final blocks and coverage results reported.
int SimulateDesign(const delta::CliOptions& opts,
                   const delta::RtlirDesign* design, delta::DiagEngine& diag,
                   delta::Arena& arena) {
  auto top = DumpTopModule(opts, design);

  delta::Scheduler scheduler(arena);
  delta::SimContext sim_ctx(scheduler, arena, diag, opts.seed);
  // §38.30 and §38.27: a PLI application's text reaches the run's standard
  // output, in order with the design's own, for as long as the run lasts.
  delta::GetGlobalVpiContext().ConnectOutputChannel(&sim_ctx.Log().Out());
  // §11.11: the run selects the same member of a min:typ:max expression that
  // ElaborateDesign folded parameters at, which EvalMinTypMax in
  // src/simulator/evaluation.cpp reads back through SimContext::GetDelayMode.
  // It is set before the design is lowered so that a delay evaluated during
  // lowering sees it.
  sim_ctx.SetDelayMode(opts.mintypmax);
  // §21.6: the plusargs $test$plusargs and $value$plusargs search.
  for (const auto& plus_arg : opts.plus_args) sim_ctx.AddPlusArg(plus_arg);
  // §31.9.4: the two timing check invocation options are in force before the
  // design's checks are registered at lowering, which builds each under them.
  sim_ctx.AcquireSpecifyManager().SetTimingCheckInvocationOptions(
      {opts.negative_timing_checks, opts.no_timing_checks});
  delta::Lowerer lowerer(sim_ctx, arena, diag);
  lowerer.Lower(design);
  // §35.4: the imports lowering registered are bound to the global symbols
  // their linkage names name, before any process can call one.
  delta::BindDesignDpiImports(sim_ctx);

  if (!opts.vcd_file.empty()) SetupVcd(sim_ctx, top, opts.vcd_file);

  scheduler.Run();
  sim_ctx.RunFinalBlocks();
  // §16.3 and §16.14.3: the results of coverage for the immediate and the
  // concurrent cover statements are reported at the end of simulation, once
  // the final blocks that could still evaluate one have run.
  delta::ReportImmediateCoverResults(sim_ctx.ImmediateCovers(), std::cout);
  delta::ReportConcurrentCoverResults(sim_ctx.ConcurrentCovers(), std::cout);
  // §19.7: the cross bins a cross's cross_num_print_missing asks the coverage
  // report to list, once the final blocks have sampled.
  sim_ctx.CoverageData().ReportMissingCrossBins(std::cout);
  // §19.9: the coverage database is saved at the end of the run to the file
  // $set_coverage_db_name named, once the final blocks have sampled.
  sim_ctx.CoverageData().SaveNamedCoverageDb();
  // §21.7.3.6.1: close the dump by recording the final simulation time, which
  // an extended VCD file ends with. This covers a dump the source's own VCD
  // tasks opened as well as one --vcd asked for, and does nothing when the run
  // opened none.
  sim_ctx.CloseVcdDump();
  delta::GetGlobalVpiContext().ConnectOutputChannel(nullptr);
  // §20.10: a $fatal or an $error the run called is an error of the run.
  return diag.HasErrors() || sim_ctx.HasRuntimeErrors() ? 1 : 0;
}

// A source that declares nothing, which is what a file of compiler directives,
// of comments alone or of no bytes at all is, is valid source text under Annex
// A.1.2 and elaborates to no design: there is nothing to run, and the run
// passes, as one of a package alone does. A run ElaborateDesign stopped on an
// error it reported fails, whatever the source declares.
int RunSimulation(const delta::CliOptions& opts,
                  const delta::LibraryMap& lib_map, delta::CompilationUnit* cu,
                  delta::DiagEngine& diag, delta::Arena& arena) {
  auto [design, failed] = ElaborateDesign(opts, lib_map, cu, diag, arena);
  if (failed) return 1;
  if (design == nullptr) return 0;
  return SimulateDesign(opts, design, diag, arena);
}

// The run to carry across the thread boundary below, and the status it
// answers.
struct SimulationJob {
  const std::function<int()>& run;
  int status = 1;
};

void* RunSimulationJob(void* arg) {
  auto* job = static_cast<SimulationJob*>(arg);
  job->status = job->run();
  return nullptr;
}

// §13.3 has a task enable other tasks with no limit on how many are enabled,
// and §13.4 lets a function call functions and itself, so a design's call
// chain is as deep as it writes it; the interpreter spends a native frame on
// every statement and call along it, and UVM's `run_test` stands ninety-odd
// frames deep before its root object exists, which outran the 8 MiB a main
// thread has on macOS and segfaulted. The simulation therefore runs on a
// thread of its own with a stack of 1 GiB, address space reserved and paged
// in only as far as the run goes, the main thread waiting for its status; a
// system that refuses the thread gets the run on the main thread as before.
//
// The attributes are set up unchecked. POSIX lets pthread_attr_init fail only
// for want of memory, which glibc and macOS never report, and
// pthread_attr_setstacksize only for a size below PTHREAD_STACK_MIN or, on
// macOS, one that is not a multiple of the page size; the constant 1 GiB is
// neither, so neither call has a failure this run could take.
int RunOnDeepStack(const std::function<int()>& run) {
  SimulationJob job{run};
  constexpr std::size_t kStackBytes = std::size_t{1} << 30;
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, kStackBytes);
  pthread_t thread{};
  int created = pthread_create(&thread, &attr, RunSimulationJob, &job);
  pthread_attr_destroy(&attr);
  if (created != 0) return run();
  pthread_join(thread, nullptr);
  return job.status;
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
    std::optional<std::string> content = delta::ReadSource(path);
    if (!content) return 1;
    auto file_id = src_mgr.AddFile(path, *content);
    std::cout << delta::EncryptEnvelopes(*content, opts.protect.exchange_key,
                                         opts.protect.keys, &diag, file_id);
  }
  return diag.HasErrors() ? 1 : 0;
}

// §33.5.4's binding invocation: the tool that binds a design from precompiled
// libraries is told only the lib.cell of each top-level cell, or the
// configuration to use, or both, and under that strategy the configuration is
// precompiled as well.
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
  // §33.8.1: -L names the libraries an instantiated cell is searched in and
  // their order, on this invocation as on one that reads source descriptions,
  // and an argument that is no library name is refused here as it is there.
  // A bind reads no library map, so the order is the -L names alone.
  std::vector<std::string> errors;
  auto order =
      delta::LibraryMap().ResolveSearchOrder(opts.lib_search_order, &errors);
  for (const auto& err : errors) std::cerr << "error: " << err << "\n";
  if (!errors.empty()) return 1;
  binder.SetLibrarySearchOrder(std::move(order));

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
  // The bound design is the design of this invocation, so it is run as one
  // elaborated from source descriptions is: --lint-only and --parse-only stop
  // short of the run, and anything else simulates it.
  if (opts.lint_only || opts.parse_only) return 0;
  // §34.5.29.2: the runtime licences the precompiled models state are asked
  // before they are executed, which here is now, and the exit functions they
  // name are called as `licenses` goes, once the simulation is over.
  delta::ProtectLicenseLibraries licenses;
  if (!delta::PrecompiledRuntimeLicensesGranted(opts.precompiled_libs, licenses,
                                                diag)) {
    return 1;
  }
  return RunOnDeepStack(
      [&] { return SimulateDesign(opts, design, diag, arena); });
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
    status = delta::RunPrecompile(opts, src_mgr, diag);
    return true;
  }
  if (!opts.precompiled_libs.empty()) {
    status = RunSeparateCompilationBind(opts, src_mgr, diag);
    return true;
  }
  return false;
}

namespace {

// §38.17: vpi_get_vlog_info() reports how many invocation options there were
// and what each one was, as argc and argv, entry zero being the tool's name.
// Nothing told the run what they were, so every invocation reported an empty
// command line. Recording it before anything else runs means the answer is
// there for whatever asks, including a PLI application loaded early.
//
// C lets a process start with argc of zero, argv[0] then being the null pointer
// that ends the list. No platform deltahdl runs on starts one that way -- Linux
// gives such a process an empty argv[0] -- but a command line with no entry
// zero is still answered with the tool's own name there, by padding the words
// to one rather than by reading argv[0].
void RecordInvocationCommandLine(int argc, char* argv[]) {
  std::vector<std::string> words(argv, argv + argc);
  words.resize(std::max<std::size_t>(words.size(), 1), "deltahdl");
  delta::GetGlobalVpiContext().SetInvocationArguments(
      words.front(), {std::next(words.begin()), words.end()});
}

}  // namespace

// §J.4.1: the bootstrap file -sv_liblist names has a syntax of its own -- the
// first line holds #!SV_LIBRARIES, each later line one entry or a comment --
// and a file that departs from it is reported at the line that does, before
// anything the file lists would be loaded. ParseForeignCodeBootstrap opens
// every description it gives with "line N: ", so the number is read from there
// unchecked for the position of the report, and the text after it is what is
// reported. False where any file is at fault.
bool BootstrapFilesAreWellFormed(const delta::CliOptions& opts,
                                 delta::SourceManager& src_mgr,
                                 delta::DiagEngine& diag,
                                 std::vector<std::string>& libraries) {
  bool ok = true;
  for (const auto& liblist : opts.sv_liblists) {
    std::ifstream ifs(liblist.path);
    if (!ifs) {
      diag.Error(delta::SourceLoc::None(),
                 "cannot open bootstrap file '" + liblist.path + "'",
                 delta::Subclause("J.4"));
      ok = false;
      continue;
    }
    std::ostringstream ss;
    ss << ifs.rdbuf();
    std::string content = ss.str();
    delta::ForeignCodeBootstrap file =
        delta::ParseForeignCodeBootstrap(content);
    if (file.Ok()) {
      // §J.4: the bootstrap file's entries are processed ahead of the -sv_lib
      // switches, each resolved against the root in force when the switch
      // naming the file was (§J.4.2 c).
      for (auto& entry :
           delta::ForeignCodeResolveBootstrapEntries(file, liblist.root)) {
        libraries.push_back(std::move(entry));
      }
      continue;
    }
    uint32_t line = 1;
    std::string message = file.error;
    std::size_t colon = message.find(": ");
    std::from_chars(message.data() + 5, message.data() + colon, line);
    message = message.substr(colon + 2);
    uint32_t file_id = src_mgr.AddFile(liblist.path, std::move(content));
    diag.Error(delta::SourceLoc{file_id, line, 1}, message,
               delta::Subclause("J.4.1"));
    ok = false;
  }
  return ok;
}

// Annex J.4: the object code the command line specifies, settled before the
// design is read -- each bootstrap file well formed, then each library it or
// an -sv_lib switch names loaded, in the order the annex processes them -- so
// that the symbols the libraries define are there to bind the design's
// imports to.
bool ForeignCodeIsLoaded(const delta::CliOptions& opts,
                         delta::SourceManager& src_mgr,
                         delta::DiagEngine& diag) {
  std::vector<std::string> bootstrap_libraries;
  return BootstrapFilesAreWellFormed(opts, src_mgr, diag,
                                     bootstrap_libraries) &&
         delta::ForeignCodeLoadLibraries(bootstrap_libraries, opts.sv_libs,
                                         diag);
}

// What the run does with a parsed compilation unit, chosen by the options
// that name a stage: --dump-ast prints the tree and goes on; --parse-only,
// "Parse only", ends the run here, after the parse's own reports have already
// returned 1, with the status --lint-only gave before it elaborated, so a
// source only the elaborator rejects passes, which is what a file meant to
// test the preprocessor or the parser alone asks for; --lint-only elaborates
// and stops; --synth synthesizes; and with none of them the design is
// simulated. Synthesis and simulation both evaluate the model, which §34.5.29.2
// NOTE 1 counts as executing it, so each begins only once `licensed` has
// answered that every runtime licence the model states is granted.
int RunParsedUnit(const delta::CliOptions& opts,
                  const delta::LibraryMap& lib_map, delta::CompilationUnit* cu,
                  delta::DiagEngine& diag,
                  const std::function<bool()>& licensed) {
  if (opts.dump_ast) {
    DumpAst(cu);
  }
  if (opts.parse_only) {
    std::cout << "parse pass: no errors\n";
    return 0;
  }

  delta::Arena elab_arena;
  if (opts.lint_only) {
    return RunLint(opts, lib_map, cu, diag, elab_arena);
  }
  if (!licensed()) return 1;
  if (opts.synth_mode) {
    return RunSynthesis(opts, lib_map, cu, diag, elab_arena);
  }
  return RunOnDeepStack(
      [&] { return RunSimulation(opts, lib_map, cu, diag, elab_arena); });
}

// --version and --help are answered with no design read, and so is an
// invocation that names nothing to read, whose help ends in a failing status.
// §33.5.4: a bind from precompiled libraries is told the top-level cells, the
// configuration, or both, and is given no source description, so --load-lib
// stands in for a source file.
bool AnsweredWithoutADesign(const delta::CliOptions& opts, int& status) {
  if (opts.show_version) {
    PrintVersion();
    status = 0;
    return true;
  }
  if (opts.show_help ||
      (opts.source_files.empty() && opts.precompiled_libs.empty())) {
    PrintHelp();
    status = opts.show_help ? 0 : 1;
    return true;
  }
  return false;
}

int main(int argc, char* argv[]) {
  RecordInvocationCommandLine(argc, argv);

  // §38.37.2: the routines placed in the vlog_startup_routines[] array are how
  // an application registers its system task and system function callbacks,
  // and does whatever else it needs, as soon as the simulator starts, so the
  // array the tool supplies is walked here, before the run decides what it
  // is doing with its arguments. A system task a PLI application registers from
  // one of these routines is then registered ahead of the compilation that
  // resolves references to it.
  delta::InvokeVlogStartupRoutines(vlog_startup_routines);

  delta::CliOptions opts;
  if (!delta::ParseArgs(argc, argv, opts)) {
    return 1;
  }
  // §36.12.2.2: the default VPI compatibility mode --vpi-compat-mode selects
  // governs every application not bound to a mode at compile time, so it is
  // set once, before the design is compiled or run and any callback an
  // application registered above is called.
  if (opts.vpi_compat_mode != 0)
    delta::GetGlobalVpiContext().SetDefaultCompatibilityMode(
        opts.vpi_compat_mode);
  int answered_status = 0;
  if (AnsweredWithoutADesign(opts, answered_status)) return answered_status;

  delta::SourceManager src_mgr;
  delta::DiagEngine diag(src_mgr);
  if (opts.werror) {
    diag.SetWarningsAsErrors(true);
  }

  if (!ForeignCodeIsLoaded(opts, src_mgr, diag)) return 1;

  int mode_status = 0;
  if (RanStandaloneMode(opts, src_mgr, diag, mode_status)) return mode_status;

  delta::LibraryMap lib_map;
  if (!LoadLibraryMaps(opts, src_mgr, lib_map)) return 1;

  // §34.5.28.2 and §34.5.29.2: the libraries a protected model's licences are
  // asked through, whose exit functions are called as this object goes, when
  // main returns.
  delta::ProtectLicenseLibraries licenses;
  auto pp = PreprocessSources(opts, src_mgr, diag, licenses);
  if (pp.unreadable || diag.HasErrors()) {
    return 1;
  }

  delta::Arena ast_arena;
  auto* cu = ParseSource(pp.source, pp.line_origins, src_mgr, diag, ast_arena);
  if (diag.HasErrors()) {
    return 1;
  }
  ApplyPreprocMetadata(cu, pp);
  if (!TagDesignElementLibraries(*cu, pp, lib_map, diag)) return 1;
  return RunParsedUnit(opts, lib_map, cu, diag, [&] {
    return delta::RuntimeLicensesGranted(pp.runtime_licenses, licenses, diag);
  });
}
