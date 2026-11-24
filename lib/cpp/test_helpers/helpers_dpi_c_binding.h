#pragma once

#include <dlfcn.h>
#include <gtest/gtest.h>

#include <cstdint>
#include <filesystem>
#include <map>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_diagnosed.h"
#include "fixture_simulator.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_binding.h"
#include "simulator/dpi_runtime.h"
#include "simulator/lowerer.h"

using namespace delta;

inline DpiSymbolLookup LookupIn(const std::map<std::string, void*>& functions) {
  auto table = std::make_shared<const std::map<std::string, void*>>(functions);
  return [table](const std::string& name) -> void* {
    auto it = table->find(name);
    return it == table->end() ? nullptr : it->second;
  };
}

inline std::filesystem::path CallBuildDir(const std::string& name) {
  std::filesystem::path dir =
      std::filesystem::path(::testing::TempDir()) / name;
  const auto* test = ::testing::UnitTest::GetInstance()->current_test_info();
  if (test == nullptr) return dir;
  return dir / (std::string(test->test_suite_name()) + "." + test->name());
}

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

inline int32_t IntVariableAfterRun(
    const std::string& src, const std::map<std::string, void*>& functions,
    const std::string& dir_name, const char* var) {
  SimFixture f;
  RunWithImportsBound(src, f, functions, dir_name);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  auto* found = f.ctx.FindVariable(var);
  EXPECT_NE(found, nullptr);
  return found == nullptr ? INT32_MIN
                          : static_cast<int32_t>(found->value.ToUint64());
}

template <typename Function>
Function NamedExport(const char* name) {
  return reinterpret_cast<Function>(dlsym(RTLD_DEFAULT, name));
}

inline uint64_t DesignValue(SimFixture& f, std::string_view name) {
  auto* found = f.ctx.FindVariable(name);
  EXPECT_NE(found, nullptr) << name;
  return found == nullptr ? ~uint64_t{0} : found->value.ToUint64();
}

inline DpiArg CFormal(std::string_view name, DataTypeKind type,
                      Direction direction, uint32_t width = 0) {
  DpiArg formal;
  formal.name = name;
  formal.type = type;
  formal.direction = direction;
  formal.width = width;
  return formal;
}

inline DpiRtFunction CImport(std::string_view name, DataTypeKind result,
                             std::vector<DpiArg> formals) {
  DpiRtFunction import;
  import.sv_name = name;
  import.c_name = name;
  import.return_type = result;
  import.args = std::move(formals);
  return import;
}

struct DpiCBinding {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Diagnosed diagnosed{diag};
  DpiRuntime dpi;

  void Bind(const std::map<std::string, void*>& functions,
            const std::string& dir_name) {
    BindDpiImports(dpi, LookupIn(functions), CallBuildDir(dir_name), "cc",
                   diag);
  }

  DpiArgValue Call(std::string_view name, std::vector<DpiArgValue>& args) {
    return dpi.CallImportWithArgs(name, args);
  }
};
