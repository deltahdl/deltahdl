// §35.3: Two layers of DPI

#include <gtest/gtest.h>
#include <cstdint>
#include <string>
#include <vector>
#include "simulation/dpi_runtime.h"

using namespace delta;

namespace {

// =============================================================================
// Pure vs context function semantics (S35.5.3)
// =============================================================================
TEST(DpiRuntime, PureFunctionFlag) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_pure";
  func.sv_name = "sv_pure";
  func.is_pure = true;
  func.is_context = false;
  func.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromInt(args[0].AsInt() + 1);
  };
  rt.RegisterImport(func);

  const auto* found = rt.FindImport("sv_pure");
  ASSERT_NE(found, nullptr);
  EXPECT_TRUE(found->is_pure);
  EXPECT_FALSE(found->is_context);
}

TEST(DpiRuntime, ContextFunctionFlag) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_ctx";
  func.sv_name = "sv_ctx";
  func.is_pure = false;
  func.is_context = true;
  func.impl = [](const std::vector<DpiArgValue>& /*args*/) -> DpiArgValue {
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(func);

  const auto* found = rt.FindImport("sv_ctx");
  ASSERT_NE(found, nullptr);
  EXPECT_FALSE(found->is_pure);
  EXPECT_TRUE(found->is_context);
}

}  // namespace
