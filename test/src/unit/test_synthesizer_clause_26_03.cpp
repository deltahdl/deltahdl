#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(PackageScopeReferenceSynthesis, PackageScopedParameterLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
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

TEST(PackageImportSynthesis, ExplicitImportLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
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

TEST(PackageImportSynthesis, WildcardImportTypeLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
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
