#pragma once

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "common/types.h"
#include "elaborator/elaborator_data.h"
#include "preprocessor/protect_cli.h"

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
  std::string output_file;
  std::string timescale;
  std::string fst_file;
  std::string format;
  std::string lib_file;
  std::string target;
  std::vector<std::string> include_dirs;
  std::vector<std::string> lib_dirs;
  std::vector<std::string> lib_files;

  std::vector<std::string> lib_search_order;
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

  std::vector<std::pair<std::string, std::string>> defines;
  uint64_t max_time = 0;
  // §27.4 bounds a loop generate scheme's iteration count nowhere, so this is
  // a budget rather than a rule. It exists so a design that generates more
  // instances than the default admits can say so, instead of being refused.
  int64_t max_generate_iterations = delta::kDefaultMaxGenerateIterations;
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
  // §11.11's choice among the three values of a min:typ:max expression, set by
  // --mintypmax. Not delay_mode above, which is the synthesizer's
  // delay-oriented optimization.
  delta::DelayMode mintypmax = delta::DelayMode::kTyp;
  // Whether an option was recognized and its argument refused. It is separate
  // from the unrecognized option ParseArgs reports, because an option that
  // names its own complaint has already printed the one a reader needs.
  bool rejected_argument = false;
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
