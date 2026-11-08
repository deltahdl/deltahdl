#include <pthread.h>
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
#include "driver/cli_options.h"
#include "driver/precompile_run.h"
#include "driver/protect_license_libraries.h"
#include "driver/source_units.h"
#include "elaborator/command_line_bind.h"
#include "elaborator/compilation_unit_set.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/separate_compilation_bind.h"
#include "parser/ast_design.h"
#include "parser/library_map.h"
#include "preprocessor/protect_cli.h"
#include "preprocessor/protect_processing.h"
#include "simulator/cover_results.h"
#include "simulator/coverage_control.h"
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

using delta::PreprocResult;

struct ParsedUnits {
  delta::CompilationUnit* cu = nullptr;
  std::vector<delta::CompilationUnit*> separate;
};

void PrintVersion() {
  std::cout << "deltahdl 0.1.0\n";
  std::cout << "SystemVerilog IEEE 1800-2023 simulator and synthesizer\n";
}

void PrintHelp() {
  PrintVersion();
  std::cout << "\nUsage: deltahdl [options] <source-files...>\n\n"
            << "General:\n"
            << "  --top <module>       Top-level module\n"
            << "  --mintypmax <val>    min:typ:max member: min, typ or max\n"
            << "  --max-generate-iterations <n>\n"
            << "                       Loop generate iteration budget "
               "(default 262144)\n"
            << "  -f <file>            Read options from file\n"
            << "  -L <name>            Library search order (repeatable)\n"
            << "  <file>.map           Library map file, read before the "
               "sources (33.3.1);\n"
            << "                       lib.map in the working directory "
               "when none is named\n"
            << "  +define+<n>=<v>      Define macro\n"
            << "  +incdir+<path>       Include directory\n"
            << "  +<plusarg>           Plusarg for $test$plusargs and "
               "$value$plusargs (21.6)\n"
            << "  -Werror              Treat warnings as errors\n"
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
            << "  --seed <n>           Random seed\n"
            << "  --vpi-compat-mode <mode>\n"
            << "                       Default VPI compatibility mode "
               "(36.12.2.2):\n"
            << "                       1364v1995, 1364v2001, 1364v2005, "
               "1800v2005, 1800v2009\n"
            << "  --negative-timing-checks\n"
            << "                       Accept negative $setuphold/$recrem "
               "limits (31.9.4)\n"
            << "  --no-timing-checks   Turn every timing check off (31.9.4)\n"
            << "  --pulse-reject-limit <percent>\n"
            << "                       Reject limit as a percentage of each "
               "path delay (30.7.2)\n"
            << "  --pulse-error-limit <percent>\n"
            << "                       Error limit as a percentage of each "
               "path delay (30.7.2)\n"
            << "  --pulse-style-onevent, --pulse-style-ondetect\n"
            << "                       Pulse filtering style for every path "
               "output (30.7.4.1)\n"
            << "  --showcancelled, --noshowcancelled\n"
            << "                       Show cancelled pulses as x on every "
               "path output, or not (30.7.4.2)\n"
            << "  -D <name>[=<value>]  Define preprocessor macro\n"
            << "  --compilation-unit-per-file\n"
            << "                       Make each source file a compilation "
               "unit (3.12.1)\n"
            << "  --lint-only          Parse and elaborate only\n"
            << "  --parse-only         Parse only\n"
            << "  --dump-ast           Print AST to stdout\n"
            << "  --dump-ir            Print RTLIR to stdout\n\n"
            << "Synthesis:\n"
            << "  --synth              Synthesis mode\n"
            << "  --config <name>      Configuration to bind (33.5.4)\n"
            << "  --load-lib <file>    Precompiled library to bind from\n"
            << "  --precompile-into <library>\n"
            << "                       Library to compile sources into\n"
            << "  --precompile-out <file>\n"
            << "                       File the precompiled cells go to\n"
            << "  --no-opt             Skip optimization passes\n"
            << "  --dump-aig           Print AIG to stdout\n";
}

void SetupVcd(delta::SimContext& ctx, const std::string& top,
              const std::string& vcd_file) {
  ctx.Vcd().SetDumpFileName(vcd_file);
  ctx.Vcd().SetDumpFileLiteral("\"" + vcd_file + "\"");
  ctx.OpenVcdDump(top, false, delta::VcdFileType::kFourState);
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
    if (!loaded) return false;
  }
  return true;
}

std::string_view SourceFileHoldingLine(const PreprocResult& pp, uint32_t line) {
  std::string_view path;
  for (const auto& [first_line, file] : pp.file_first_lines) {
    if (first_line > line) break;
    path = file;
  }
  return path;
}

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

void AddMapConfigs(delta::CompilationUnit& cu,
                   const delta::LibraryMap& lib_map) {
  for (auto* cfg : lib_map.DeclaredConfigs()) cu.configs.push_back(cfg);
}

std::string_view SourceTopModule(const delta::CliOptions& opts) {
  if (opts.top_modules.empty()) return {};
  return opts.top_modules.back();
}

std::string DumpTopModule(const delta::CliOptions& opts,
                          const delta::RtlirDesign* design) {
  if (std::string_view top = SourceTopModule(opts); !top.empty()) {
    return std::string(top);
  }
  if (design->top_modules.empty()) return "";
  return std::string(design->top_modules.front()->name);
}

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

struct Elaboration {
  const delta::RtlirDesign* design = nullptr;
  bool failed = false;
};

Elaboration ElaborateDesign(const delta::CliOptions& opts,
                            const delta::LibraryMap& lib_map,
                            const ParsedUnits& units, delta::DiagEngine& diag,
                            delta::Arena& arena) {
  delta::DelayModeGuard mintypmax_guard(opts.mintypmax);

  std::optional<delta::Elaborator> built;
  if (units.separate.empty()) {
    built.emplace(arena, diag, units.cu);
  } else {
    built.emplace(arena, diag, units.separate);
  }
  delta::Elaborator& elaborator = *built;
  elaborator.SetMaxGenerateIterations(opts.max_generate_iterations);

  if (!InstallLibrarySearchOrder(opts, lib_map, elaborator)) {
    return {.failed = true};
  }
  const auto* design = delta::ElaborateCommandLine(
      elaborator, *units.cu, SourceTopModule(opts), opts.config, diag);
  if (diag.HasErrors()) return {.failed = true};
  if (design == nullptr) return {.failed = !units.cu->DeclaresNothing()};
  if (opts.dump_ir) DumpIr(design);
  return {.design = design};
}

int RunSynthesis(const delta::CliOptions& opts,
                 const delta::LibraryMap& lib_map, const ParsedUnits& units,
                 delta::DiagEngine& diag, delta::Arena& arena) {
  auto [design, failed] = ElaborateDesign(opts, lib_map, units, diag, arena);
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

int RunLint(const delta::CliOptions& opts, const delta::LibraryMap& lib_map,
            const ParsedUnits& units, delta::DiagEngine& diag,
            delta::Arena& arena) {
  if (ElaborateDesign(opts, lib_map, units, diag, arena).failed) return 1;
  std::cout << "lint pass: no errors\n";
  return 0;
}

int SimulateDesign(const delta::CliOptions& opts,
                   const delta::RtlirDesign* design, delta::DiagEngine& diag,
                   delta::Arena& arena) {
  auto top = DumpTopModule(opts, design);

  delta::Scheduler scheduler(arena);
  delta::SimContext sim_ctx(scheduler, arena, diag, opts.seed);
  delta::GetGlobalVpiContext().ConnectOutputChannel(&sim_ctx.Log().Out());
  sim_ctx.SetDelayMode(opts.mintypmax);
  for (const auto& plus_arg : opts.plus_args) sim_ctx.AddPlusArg(plus_arg);
  sim_ctx.AcquireSpecifyManager().SetTimingCheckInvocationOptions(
      {opts.negative_timing_checks, opts.no_timing_checks});
  delta::ApplyPulseControlOptions(opts, sim_ctx.AcquireSpecifyManager());
  sim_ctx.GetCoverageControlState().SetDatabaseDirectory(".");
  delta::Lowerer lowerer(sim_ctx, arena, diag);
  lowerer.Lower(design);
  delta::BindDesignDpiImports(sim_ctx);

  if (!opts.vcd_file.empty()) SetupVcd(sim_ctx, top, opts.vcd_file);

  scheduler.Run();
  scheduler.EndSimulation();
  delta::ReportImmediateCoverResults(sim_ctx.ImmediateCovers(), std::cout);
  delta::ReportConcurrentCoverResults(sim_ctx.ConcurrentCovers(), std::cout);
  sim_ctx.CoverageData().ReportMissingCrossBins(std::cout);
  sim_ctx.CoverageData().SaveNamedCoverageDb();
  sim_ctx.CloseVcdDump();
  delta::GetGlobalVpiContext().ConnectOutputChannel(nullptr);
  return diag.HasErrors() || sim_ctx.HasRuntimeErrors() ? 1 : 0;
}

int RunSimulation(const delta::CliOptions& opts,
                  const delta::LibraryMap& lib_map, const ParsedUnits& units,
                  delta::DiagEngine& diag, delta::Arena& arena) {
  auto [design, failed] = ElaborateDesign(opts, lib_map, units, diag, arena);
  if (failed) return 1;
  if (design == nullptr) return 0;
  return SimulateDesign(opts, design, diag, arena);
}

struct SimulationJob {
  const std::function<int()>& run;
  int status = 1;
};

void* RunSimulationJob(void* arg) {
  auto* job = static_cast<SimulationJob*>(arg);
  job->status = job->run();
  return nullptr;
}

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

int RunEnvelopeEncryption(const delta::CliOptions& opts,
                          delta::SourceManager& src_mgr,
                          delta::DiagEngine& diag) {
  delta::EnvelopeEncryptor encryptor(opts.protect.exchange_key,
                                     opts.protect.keys, &diag);
  for (const auto& path : opts.source_files) {
    std::optional<std::string> content = delta::ReadSource(path);
    if (!content) return 1;
    auto file_id = src_mgr.AddFile(path, *content);
    std::cout << encryptor.Encrypt(src_mgr.FileContent(file_id), file_id);
  }
  std::cout << encryptor.Finish();
  return diag.HasErrors() ? 1 : 0;
}

int RunSeparateCompilationBind(const delta::CliOptions& opts,
                               delta::SourceManager& src_mgr,
                               delta::DiagEngine& diag) {
  delta::Arena arena;
  delta::SeparateCompilationBinder binder(src_mgr, arena, diag);
  for (const auto& path : opts.precompiled_libs) {
    if (!binder.LoadLibrary(path)) return 1;
  }
  std::vector<std::string> errors;
  auto order =
      delta::LibraryMap().ResolveSearchOrder(opts.lib_search_order, &errors);
  for (const auto& err : errors) std::cerr << "error: " << err << "\n";
  if (!errors.empty()) return 1;
  binder.SetLibrarySearchOrder(std::move(order));

  const delta::RtlirDesign* design = nullptr;
  if (!opts.config.empty()) {
    design = binder.BindConfig(opts.config);
  } else if (!opts.top_modules.empty()) {
    design = binder.Bind(std::vector<std::string_view>(opts.top_modules.begin(),
                                                       opts.top_modules.end()));
  } else {
    std::cerr << "a separate compilation bind names --config or --top\n";
    return 1;
  }
  if (design == nullptr || diag.HasErrors()) return 1;
  if (opts.dump_ir) DumpIr(design);
  if (opts.lint_only || opts.parse_only) return 0;
  delta::ProtectLicenseLibraries licenses;
  if (!delta::PrecompiledRuntimeLicensesGranted(opts.precompiled_libs, licenses,
                                                diag)) {
    return 1;
  }
  return RunOnDeepStack(
      [&] { return SimulateDesign(opts, design, diag, arena); });
}

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

void RecordInvocationCommandLine(int argc, char* argv[]) {
  std::vector<std::string> words(argv, argv + argc);
  words.resize(std::max<std::size_t>(words.size(), 1), "deltahdl");
  delta::GetGlobalVpiContext().SetInvocationArguments(
      words.front(), {std::next(words.begin()), words.end()});
}

}  // namespace

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

bool ForeignCodeIsLoaded(const delta::CliOptions& opts,
                         delta::SourceManager& src_mgr,
                         delta::DiagEngine& diag) {
  std::vector<std::string> bootstrap_libraries;
  return BootstrapFilesAreWellFormed(opts, src_mgr, diag,
                                     bootstrap_libraries) &&
         delta::ForeignCodeLoadLibraries(bootstrap_libraries, opts.sv_libs,
                                         diag);
}

int RunParsedUnit(const delta::CliOptions& opts,
                  const delta::LibraryMap& lib_map, const ParsedUnits& units,
                  delta::DiagEngine& diag,
                  const std::function<bool()>& licensed) {
  if (opts.dump_ast) {
    DumpAst(units.cu);
  }
  if (opts.parse_only) {
    std::cout << "parse pass: no errors\n";
    return 0;
  }

  delta::Arena elab_arena;
  if (opts.lint_only) {
    return RunLint(opts, lib_map, units, diag, elab_arena);
  }
  if (!licensed()) return 1;
  if (opts.synth_mode) {
    return RunSynthesis(opts, lib_map, units, diag, elab_arena);
  }
  return RunOnDeepStack(
      [&] { return RunSimulation(opts, lib_map, units, diag, elab_arena); });
}

int RunSeparateUnits(const delta::CliOptions& opts,
                     const delta::LibraryMap& lib_map,
                     delta::SourceManager& src_mgr, delta::DiagEngine& diag,
                     delta::ProtectLicenseLibraries& licenses) {
  delta::Arena ast_arena;
  delta::SeparateUnits parsed =
      delta::ParseSeparateUnits(opts, src_mgr, diag, licenses, ast_arena);
  if (!parsed.read) return 1;
  ParsedUnits units;
  bool tagged = true;
  for (auto& unit : parsed.units) {
    tagged &= TagDesignElementLibraries(*unit.cu, unit.pp, lib_map, diag);
    units.separate.push_back(unit.cu);
  }
  if (!tagged) return 1;
  units.cu = delta::PoolCompilationUnits(units.separate, ast_arena).merged;
  AddMapConfigs(*units.cu, lib_map);
  return RunParsedUnit(opts, lib_map, units, diag, [&] {
    return delta::RuntimeLicensesGranted(
        parsed.units.back().pp.runtime_licenses, licenses, diag);
  });
}

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

  delta::InvokeVlogStartupRoutines(vlog_startup_routines);

  delta::CliOptions opts;
  if (!delta::ParseArgs(argc, argv, opts)) {
    return 1;
  }
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

  delta::ProtectLicenseLibraries licenses;
  if (opts.compilation_unit_per_file) {
    return RunSeparateUnits(opts, lib_map, src_mgr, diag, licenses);
  }
  auto pp = delta::PreprocessSources(opts, src_mgr, diag, licenses);
  if (pp.unreadable || diag.HasErrors()) {
    return 1;
  }

  delta::Arena ast_arena;
  auto* cu = delta::ParseSource(pp, src_mgr, diag, ast_arena);
  if (diag.HasErrors()) {
    return 1;
  }
  delta::ApplyPreprocMetadata(cu, pp);
  if (!TagDesignElementLibraries(*cu, pp, lib_map, diag)) return 1;
  AddMapConfigs(*cu, lib_map);
  return RunParsedUnit(opts, lib_map, ParsedUnits{cu, {}}, diag, [&] {
    return delta::RuntimeLicensesGranted(pp.runtime_licenses, licenses, diag);
  });
}
