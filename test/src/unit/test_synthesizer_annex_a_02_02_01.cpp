#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(NetAndVariableTypeSynthesis, IntegerVectorTypeLogicLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [3:0] a;\n"
                           "  assign a = 4'h5;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(NetAndVariableTypeSynthesis, IntegerVectorTypeBitLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  bit [7:0] b;\n"
                           "  assign b = 8'h0F;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(NetAndVariableTypeSynthesis, NetTypeWireLowers) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input wire [1:0] i, output wire [1:0] o);\n"
                   "  assign o = i;\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(NetAndVariableTypeSynthesis, SigningSignedLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic signed [3:0] x;\n"
                           "  assign x = -4'sd1;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(NetAndVariableTypeSynthesis, StructUnionPackedMemberLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  typedef struct packed {\n"
                           "    logic [3:0] hi;\n"
                           "    logic [3:0] lo;\n"
                           "  } s_t;\n"
                           "  s_t s;\n"
                           "  assign s = 8'hF0;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(NetAndVariableTypeSynthesis, EnumTypeLowers) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m;\n"
                   "  typedef enum logic [1:0] { A = 0, B = 1, C = 2 } e_t;\n"
                   "  e_t e;\n"
                   "  assign e = B;\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(NetAndVariableTypeSynthesis, PackedDimensionFromParameterLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  parameter int W = 6;\n"
                           "  logic [W-1:0] bus;\n"
                           "  assign bus = '0;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(NetAndVariableTypeSynthesis, NetTypeWandLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  wand [1:0] w;\n"
                           "  assign w = 2'b01;\n"
                           "  assign w = 2'b10;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
