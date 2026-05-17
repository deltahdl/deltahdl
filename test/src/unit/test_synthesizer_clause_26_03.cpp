#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// §26.3 example: `ComplexPkg::Complex cout = ComplexPkg::mul(a, b);` — the
// scope resolution operator must bring a package parameter into the design
// in a form the synthesizer can lower.
TEST(PackageScopeReferenceSynthesis, PackageScopedParameterLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "package pkg;\n"
      "  parameter int WIDTH = 8;\n"
      "endpackage\n"
      "module top;\n"
      "  logic [pkg::WIDTH-1:0] data;\n"
      "  assign data = '0;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §26.3: an explicit `import pkg::WIDTH;` makes the imported identifier
// directly visible in the importing scope.  Synthesis must accept the
// imported name in dimensions just as it does a local parameter.
TEST(PackageImportSynthesis, ExplicitImportLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "package pkg;\n"
      "  parameter int WIDTH = 4;\n"
      "endpackage\n"
      "module top;\n"
      "  import pkg::WIDTH;\n"
      "  logic [WIDTH-1:0] data;\n"
      "  assign data = '0;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §26.3: a wildcard import `import pkg::*;` brings package types into the
// importing scope; synthesis must lower a design that names a
// package-declared type by its unqualified name post-wildcard.
TEST(PackageImportSynthesis, WildcardImportTypeLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "package pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "module top;\n"
      "  import pkg::*;\n"
      "  byte_t data;\n"
      "  assign data = 8'h00;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
