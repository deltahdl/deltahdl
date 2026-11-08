#pragma once

#include <filesystem>
#include <fstream>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "driver/cli_options.h"
#include "driver/precompile_run.h"
#include "elaborator/rtlir.h"
#include "elaborator/separate_compilation_bind.h"
#include "fixture_scratch_dir.h"

using namespace delta;

inline RtlirDesign* BoundFromALibrary(const ScratchDir& tmp,
                                      const std::vector<std::string>& sources,
                                      std::string_view key,
                                      SeparateCompilationBinder& binder) {
  CliOptions opts;
  for (const std::string& source : sources) {
    const std::string kPath =
        (tmp.dir /
         ("source" + std::to_string(opts.source_files.size()) + ".sv"))
            .string();
    std::ofstream(kPath) << source;
    opts.source_files.push_back(kPath);
  }
  opts.precompile_library = "ip";
  opts.precompile_output = (tmp.dir / "ip.dpl").string();
  opts.protect.exchange_key = std::string(key);
  SourceManager compile_mgr;
  DiagEngine compile_diag{compile_mgr};
  if (RunPrecompile(opts, compile_mgr, compile_diag) != 0) return nullptr;
  if (!binder.LoadLibrary(opts.precompile_output)) return nullptr;
  return binder.Bind({"t"});
}
