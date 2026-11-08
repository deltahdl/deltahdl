#include <gtest/gtest.h>

#include <cstdint>
#include <stdexcept>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

TEST(DpiCppImplementation, AnImportedSubroutineMayThrowAndCatchWithinItself) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_guarded";
  func.sv_name = "sv_guarded";
  func.return_type = DataTypeKind::kInt;
  func.impl = [](const std::vector<DpiArgValue>&) {
    int32_t answer = 0;
    try {
      throw std::runtime_error("handled inside the imported subroutine");
    } catch (const std::runtime_error&) {
      answer = 42;
    }
    return DpiArgValue::FromInt(answer);
  };
  rt.RegisterImport(func);

  EXPECT_EQ(rt.CallImport("sv_guarded", {}).AsInt(), 42);
}

TEST(DpiCppImplementation, AnExceptionCaughtWithinAnImportUnwindsItsLocals) {
  DpiRuntime rt;
  bool unwound = false;

  struct Guard {
    bool* flag;
    ~Guard() { *flag = true; }
  };

  DpiRtFunction func;
  func.c_name = "c_unwind";
  func.sv_name = "sv_unwind";
  func.return_type = DataTypeKind::kInt;
  func.impl = [&unwound](const std::vector<DpiArgValue>&) {
    int32_t answer = 0;
    try {
      Guard guard{&unwound};
      throw std::runtime_error("thrown past a local with a destructor");
    } catch (const std::runtime_error&) {
      answer = 7;
    }
    return DpiArgValue::FromInt(answer);
  };
  rt.RegisterImport(func);

  const DpiArgValue kResult = rt.CallImport("sv_unwind", {});

  EXPECT_TRUE(unwound);
  EXPECT_EQ(kResult.AsInt(), 7);
}

}  // namespace
