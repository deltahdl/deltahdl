#include <gtest/gtest.h>

#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

// §35.5.2: a pure function call may be eliminated when its result is unused,
// or replaced by a previously memoized result when the same input values
// recur. The DPI runtime carries an is_pure flag on each registered import
// so call-elision and memoization passes can identify candidates without
// re-inspecting the elaborated AST.

TEST(PureDpiImportRegistry, PureFlagSurvivesRegistration) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_p";
  func.sv_name = "sv_p";
  func.return_type = DataTypeKind::kInt;
  func.is_pure = true;
  rt.RegisterImport(std::move(func));

  const auto* found = rt.FindImport("sv_p");
  ASSERT_NE(found, nullptr);
  EXPECT_TRUE(found->is_pure);
}

TEST(PureDpiImportRegistry, NonPureImportDistinguishable) {
  // A regular import (no pure property) round-trips with is_pure cleared so
  // optimization passes do not mis-classify it as elidable.
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_n";
  func.sv_name = "sv_n";
  func.return_type = DataTypeKind::kInt;
  rt.RegisterImport(std::move(func));

  const auto* found = rt.FindImport("sv_n");
  ASSERT_NE(found, nullptr);
  EXPECT_FALSE(found->is_pure);
}

}  // namespace
