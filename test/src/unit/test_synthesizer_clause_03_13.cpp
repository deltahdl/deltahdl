#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// §3.13(e): "The module name space ... unifies the definition of modules,
// interfaces, programs, checkers, functions, tasks, named blocks, instance
// names, parameters, named events, net declarations, variable
// declarations, and user-defined types within the enclosing construct."
// Synthesis must lower a module whose name space contains a parameter, a
// net, and an instance — exercising several entries in a single module
// name space.
TEST(NameSpaceSynthesis, ModuleNameSpaceLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module child;\n"
      "  logic sig;\n"
      "endmodule\n"
      "module top;\n"
      "  parameter int P = 4;\n"
      "  logic [P-1:0] data;\n"
      "  child c();\n"
      "  assign data = '0;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §3.13(g): "A port name introduced in the port name space can be
// reintroduced in the module name space by declaring a variable or a net
// with the same name as the port name."  Synthesis must lower a non-ANSI
// header where the port is reintroduced as an internal net.
TEST(NameSpaceSynthesis, PortReintroducedAsNetLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module top(data);\n"
      "  input data;\n"
      "  wire data;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §3.13(c) closing rule: within the compilation-unit scope name space, a
// name shall not be redeclared.  Two CU-scope typedefs of the same name
// must be rejected by the elaborator before reaching the synthesizer.
TEST(NameSpaceSynthesis, DuplicateCuScopeTypedefRejectedBeforeSynth) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "typedef int t;\n"
      "typedef int t;\n"
      "module top;\n"
      "endmodule\n");
  EXPECT_TRUE(f.diag.HasErrors());
  if (mod) {
    SynthLower synth(f.arena, f.diag);
    (void)synth.Lower(mod);
  }
}

}  // namespace
