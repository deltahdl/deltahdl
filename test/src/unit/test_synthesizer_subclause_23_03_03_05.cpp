
#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

namespace {

TEST(UnpackedArrayPortsAndArraysOfInstancesSynthesis,
     ScalarConnectionToInstanceArraySynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module child(input [7:0] i, output [7:0] o);\n"
      "  assign o = i;\n"
      "endmodule\n"
      "module top(input [7:0] x, output [7:0] y0, output [7:0] y1);\n"
      "  child c[1:0](.i(x), .o({y1, y0}));\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

// The test fails on a run that refuses `top`, whose two assignments to the
// elements of `arr` §11.5.2 addressing now lowers: `[2]` declares the addresses
// 0 and 1, and each names eight bits of the array's storage.
//
// What the case asserts is that the module lowers, not what `y0` and `y1`
// carry. `SynthLower::Lower` walks the assignments and processes of the one
// module it is given, and an instance stays behind `RtlirModuleInst::resolved`,
// so the child that drives those outputs is not part of this netlist and its
// outputs stand at constant false whatever `arr` holds. The two cases above
// assert the same of a scalar and a packed connection.
TEST(UnpackedArrayPortsAndArraysOfInstancesSynthesis,
     UnpackedArrayConnectionToInstanceArrayLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module child(input [7:0] i, output [7:0] o);\n"
                           "  assign o = i;\n"
                           "endmodule\n"
                           "module top(input [7:0] a, input [7:0] b,\n"
                           "           output [7:0] y0, output [7:0] y1);\n"
                           "  logic [7:0] arr [2];\n"
                           "  assign arr[0] = a;\n"
                           "  assign arr[1] = b;\n"
                           "  child c[1:0](.i(arr), .o({y1, y0}));\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnpackedArrayPortsAndArraysOfInstancesSynthesis,
     PackedArrayConnectionToInstanceArraySynthesizes) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module child(input [7:0] i, output [7:0] o);\n"
                   "  assign o = i;\n"
                   "endmodule\n"
                   "module top(input [15:0] bus, output [15:0] result);\n"
                   "  child c[1:0](.i(bus), .o(result));\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
