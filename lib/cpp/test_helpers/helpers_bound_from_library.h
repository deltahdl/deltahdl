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

// `sources` written to files in `tmp`, in order, and compiled by one
// invocation into library "ip" there (§33.5.3), one record per file, decrypting
// their envelopes under the exchange key `key`; and the design rooted at `t`
// bound from that library by `binder`, as another invocation binds it
// (§33.5.4), reading the compiled form and never the sources. A cell a later
// file declares again replaces the one an earlier file wrote (§33.3.1). Null
// where the compile or the bind fails.
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
