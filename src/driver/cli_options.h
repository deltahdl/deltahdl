#pragma once

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "common/arg_origin.h"
#include "common/types.h"
#include "elaborator/elaborator_data.h"
#include "preprocessor/protect_cli.h"
#include "simulator/foreign_code.h"

namespace delta {

// What the command line said, and the reading of it.
//
// The struct and ParseArgs live here rather than in src/main.cpp so that a test
// can name them. Every option below is one this tool answers for, and an option
// that reached the wrong field, or stopped being recognized, changed nothing
// any test could see while they were in that file's anonymous namespace; issue
// #3425 is that gap.
struct CliOptions {
  std::vector<std::string> source_files;
  std::string top_module;
  std::string vcd_file;
  std::vector<std::string> include_dirs;

  std::vector<std::string> lib_search_order;
  // §33.3.1 (printed page 935): "all compliant tools shall provide a mechanism
  // to specify one or more library map files to be used for a particular
  // invocation of the tool". A command-line word ending in .map is one, read
  // in the order written and ahead of every source description.
  std::vector<std::string> library_map_files;
  // §33.5.4: "the tool that actually does the binding only needs to be given
  // the lib.cell specification for the top-level cell(s) and/or the config to
  // be used". `config` is that config, named by --config, and
  // `precompiled_libs` are the files --load-lib names for the separate
  // compilation flow of §33.5.3, whose cells "shall persist" between the
  // invocation that compiled them and the one that binds them.
  std::string config;
  std::vector<std::string> precompiled_libs;
  // The library --precompile-into compiles this invocation's source
  // descriptions into, and the file it writes them to. §33.5.3 has a separate
  // compilation tool put cells into a library that a later invocation binds
  // from, and both are needed: a cell belongs to a library and the compiled
  // form has to live somewhere.
  std::string precompile_library;
  std::string precompile_output;
  // Annex J.3: the directory -sv_root gives, prepended to every relative
  // path name the annex's switches specify after it; empty while none was
  // given, the user's current working directory then being the default.
  std::string sv_root;
  // Annex J.4: the path names -sv_lib and -sv_liblist gave, each in order of
  // occurrence and each resolved as it was processed against the root then
  // in force, so that a relative name written before -sv_root resolves
  // against the working directory and one written after against the root.
  // §J.4.2 c) has a bootstrap file's entries resolve against that same root,
  // which each -sv_liblist keeps beside the file's location.
  std::vector<std::string> sv_libs;
  std::vector<ForeignCodeLibList> sv_liblists;

  std::vector<std::pair<std::string, std::string>> defines;
  // §21.6 (printed page 680): the plusargs, the arguments "provided to the
  // simulation" that "are visually distinguished from other simulator
  // arguments by their starting with the plus (+) character", each kept
  // without that sign, which $test$plusargs and $value$plusargs match without.
  std::vector<std::string> plus_args;
  // §27.4 bounds a loop generate scheme's iteration count nowhere, so this is
  // a budget rather than a rule. It exists so a design that generates more
  // instances than the default admits can say so, instead of being refused.
  int64_t max_generate_iterations = delta::kDefaultMaxGenerateIterations;
  uint32_t seed = 0;
  bool synth_mode = false;
  bool lint_only = false;
  // --parse-only stops after the parse, where --lint-only stops after the
  // elaboration: a source only the elaborator rejects passes under it.
  bool parse_only = false;
  bool dump_ast = false;
  bool dump_ir = false;
  bool dump_aig = false;
  bool no_opt = false;
  bool werror = false;
  bool show_version = false;
  bool show_help = false;
  // §11.11's choice among the three values of a min:typ:max expression, set by
  // --mintypmax.
  delta::DelayMode mintypmax = delta::DelayMode::kTyp;
  // §36.12.2.2's default VPI compatibility mode for the run, selected by
  // --vpi-compat-mode: one of the vpiCompatibilityMode values Annex M's
  // sv_vpi_user.h defines, vpiMode1364v1995 through vpiMode1800v2009, and 0
  // while none was selected, every application then observing this standard's
  // behavior.
  int vpi_compat_mode = 0;
  // §31.9.4's two invocation options: the one that enables negative values in
  // $setuphold and $recrem (--negative-timing-checks) and the one that turns
  // every timing check off (--no-timing-checks).
  bool negative_timing_checks = false;
  bool no_timing_checks = false;
  // Whether an option was recognized and its argument refused. It is separate
  // from the unrecognized option ParseArgs reports, because an option that
  // names its own complaint has already printed the one a reader needs.
  bool rejected_argument = false;
  // Where the words the parse is reading came from, while they came from an
  // options file. Null while the command line itself is read, which is the case
  // a report says nothing about: -f is what puts a word somewhere a reader
  // cannot see, and the command line is in front of them. Set and restored
  // around each file the parse descends into, so a nested file names itself
  // rather than the one that named it.
  const ArgOrigins* arg_origins = nullptr;
  // §34.3.1's encrypting mode, and the keys it needs.
  delta::ProtectCliOptions protect;
};

// Reads `argc`/`argv` into `opts`, returning false where an option was not
// recognized or its argument was refused. An unrecognized option is reported
// here; an option that refused its own argument has already reported and sets
// CliOptions::rejected_argument, which is what tells the two apart.
//
// A `-f` argument names a file of further options, which is read in place and
// may name another, so the options a command line carries are not only the ones
// written on it.
bool ParseArgs(int argc, char* argv[], CliOptions& opts);

}  // namespace delta
