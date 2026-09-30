#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <filesystem>
#include <map>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_simulator.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_binding.h"
#include "simulator/dpi_runtime.h"
#include "simulator/lowerer.h"

using namespace delta;

// A lookup finding each name in `functions`, the C functions a test binary
// defines standing in for the global symbols of a loaded library.
inline DpiSymbolLookup LookupIn(const std::map<std::string, void*>& functions) {
  return [functions](const std::string& name) -> void* {
    auto it = functions.find(name);
    return it == functions.end() ? nullptr : it->second;
  };
}

// The directory under the test's temporary directory a binding builds its
// calls in.
inline std::filesystem::path CallBuildDir(const std::string& name) {
  return std::filesystem::path(::testing::TempDir()) / name;
}

// Elaborates and lowers `src`, binds the imports it declares to `functions`
// with the C compiler `compiler`, building in `dir_name`, and runs it. The
// fixture keeps the run's variables and diagnostics for the test to read.
inline void RunWithImportsBound(const std::string& src, SimFixture& f,
                                const std::map<std::string, void*>& functions,
                                const std::string& dir_name,
                                const std::string& compiler = "cc") {
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  ASSERT_NE(f.ctx.GetDpiRuntime(), nullptr);
  BindDpiImports(*f.ctx.GetDpiRuntime(), LookupIn(functions),
                 CallBuildDir(dir_name), compiler, f.diag);
  f.scheduler.Run();
}

// A formal of an import declaration, as the registration of one records it.
inline DpiArg CFormal(std::string_view name, DataTypeKind type,
                      Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = name;
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

// An import declaration named `name` in SystemVerilog and in C alike.
inline DpiRtFunction CImport(std::string_view name, DataTypeKind result,
                             std::vector<DpiArg> formals) {
  DpiRtFunction import;
  import.sv_name = name;
  import.c_name = name;
  import.return_type = result;
  import.args = std::move(formals);
  return import;
}

// Imports bound to C functions this test binary defines rather than to ones a
// loaded library does: each is found under its linkage name in a table instead
// of among the process's global symbols, and the binding is otherwise the
// run's own -- the calls are generated as C, built with the system C compiler
// and called with the prototype §H.8 gives each declaration.
struct DpiCBinding {
  SourceManager mgr;
  DiagEngine diag{mgr};
  DpiRuntime dpi;

  // Binds every import registered on `dpi` to the function `functions` maps
  // its linkage name to, building the calls in the directory `dir_name` under
  // the test's temporary directory.
  void Bind(const std::map<std::string, void*>& functions,
            const std::string& dir_name) {
    BindDpiImports(dpi, LookupIn(functions), CallBuildDir(dir_name), "cc",
                   diag);
  }

  // Calls the import `name` with `args`, as a call site does (§35.5.1.2).
  DpiArgValue Call(std::string_view name, std::vector<DpiArgValue>& args) {
    return dpi.CallImportWithArgs(name, args);
  }
};
