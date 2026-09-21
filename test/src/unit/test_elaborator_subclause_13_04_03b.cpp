#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// The resolved value of the named localparam of the single elaborated top
// module, or -1 where it is absent or was left unresolved, so that a fold that
// never happened is told from one that happened (§13.4.3), as in
// test_elaborator_subclause_13_04_03a.cpp.
int64_t ResolvedParam(RtlirDesign* design, std::string_view name) {
  if (!design || design->top_modules.empty()) return -1;
  for (const auto& p : design->top_modules[0]->params) {
    if (p.name == name) return p.is_resolved ? p.resolved_value : -1;
  }
  return -1;
}

// §13.4.3 lets a constant function be declared in a package and called in a
// parameter initializer, and §26.3 names a package's function through the
// package scope resolution operator or an import (printed pages 345 and 808
// of IEEE 1800-2023). The folder registered a module's own functions
// alone and declined a call with no bare callee, so `pk::twice(6)` never folded
// and P was left unresolved.
TEST(ConstantFunctionElaboration, PackageFunctionThroughPackageScopeFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pk;\n"
      "  function automatic int twice(int a); return a * 2; endfunction\n"
      "endpackage\n"
      "module m;\n"
      "  localparam int P = pk::twice(6);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(ResolvedParam(design, "P"), 12);
}

// The same function reached by a wildcard import, with its defaulted second
// argument (§13.5.3) left to the default, and through the package scope with
// both actuals written: 6 * 2 and 7 * 1.
TEST(ConstantFunctionElaboration, ImportedPackageFunctionWithDefaultFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pk;\n"
      "  function automatic int twice(int a, int b = 2); return a * b;\n"
      "  endfunction\n"
      "endpackage\n"
      "module m;\n"
      "  import pk::*;\n"
      "  localparam int P = twice(6);\n"
      "  localparam int Q = pk::twice(7, 1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(ResolvedParam(design, "P"), 12);
  EXPECT_EQ(ResolvedParam(design, "Q"), 7);
}

// An explicit import names the one function it imports (§26.3): the other
// package function stays unreachable by its bare name, and the localparam
// naming it is left unresolved rather than folded.
TEST(ConstantFunctionElaboration, ExplicitImportBringsInTheNamedFunctionAlone) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pk;\n"
      "  function automatic int twice(int a); return a * 2; endfunction\n"
      "  function automatic int thrice(int a); return a * 3; endfunction\n"
      "endpackage\n"
      "module m;\n"
      "  import pk::twice;\n"
      "  localparam int P = twice(5);\n"
      "  localparam int Q = thrice(5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(ResolvedParam(design, "P"), 10);
  EXPECT_EQ(ResolvedParam(design, "Q"), -1);
}

}  // namespace
