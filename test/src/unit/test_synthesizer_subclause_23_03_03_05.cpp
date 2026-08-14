
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

// The test fails on a run that answers a netlist for `top`, whose assignments
// to the elements of `arr` the synthesizer never lowers. §11.5.2 defines array
// addressing, `mem_name[addr_expr]`, and this synthesizer builds nothing for it
// in either direction, so `assign arr[0] = a;` has no lowering and
// `SynthLower::Lower` answers null.
//
// Until this change the case asserted only that `SynthLower::Lower` answered a
// graph. That held while both assignments were dropped from the graph in
// silence, so what it was asserting over was a netlist that never drives `arr`
// and therefore feeds the instance array nothing. The case names the report as
// well as the null answer, so it states which rule fired rather than passing on
// any refusal the run happens to make.
TEST(UnpackedArrayPortsAndArraysOfInstancesSynthesis,
     AssignToAnUnpackedArrayElementIsReportedRatherThanDropped) {
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
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment target has no lowering", 7, ""));
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
