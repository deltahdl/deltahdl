
#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

namespace {

// --- R2: Scalar connection replicated to array of instances ---

TEST(UnpackedArrayPortsAndArraysOfInstancesSynthesis,
     ScalarConnectionToInstanceArraySynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
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

// --- R3: Unpacked array connection to instance array ---

TEST(UnpackedArrayPortsAndArraysOfInstancesSynthesis,
     UnpackedArrayConnectionToInstanceArraySynthesizes) {
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
}

// --- R4: Packed array connection part-selected across instances ---

TEST(UnpackedArrayPortsAndArraysOfInstancesSynthesis,
     PackedArrayConnectionToInstanceArraySynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
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
