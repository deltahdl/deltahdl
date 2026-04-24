// §28.11

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// The (highz0, highz1) pair is rejected regardless of which host construct
// carries the strength spec: gate instances, net declarations, and continuous
// assignments all share the same rule.
TEST(StrengthPairElaboration, GateInstanceHighz0Highz1IsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire o, i;\n"
      "  buf (highz0, highz1) b1 (o, i);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StrengthPairElaboration, GateInstanceHighz1Highz0IsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire o, i;\n"
      "  buf (highz1, highz0) b1 (o, i);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StrengthPairElaboration, NetDeclHighz0Highz1IsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (highz0, highz1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StrengthPairElaboration, NetDeclHighz1Highz0IsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (highz1, highz0) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StrengthPairElaboration, ContAssignHighz0Highz1IsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz0, highz1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StrengthPairElaboration, ContAssignHighz1Highz0IsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz1, highz0) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// A single-side highz (paired with any other strength) is still valid — only
// the both-sides-highz combination is singled out as illegal.
TEST(StrengthPairElaboration, GateInstanceHighz0WithStrong1IsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire o, i;\n"
      "  buf (highz0, strong1) b1 (o, i);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// A fully specified non-highz pair elaborates without any strength-related
// complaint.
TEST(StrengthPairElaboration, GateInstanceStrongPairIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire o, i;\n"
      "  buf (strong0, strong1) b1 (o, i);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// The four driving strengths (supply, strong, pull, weak) each propagate
// from a gate output. Verifying each in turn ensures none of the four
// names is accidentally rejected at the elaboration stage.
TEST(StrengthPairElaboration, GateInstanceSupplyPairIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire o, i;\n"
      "  buf (supply0, supply1) b1 (o, i);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StrengthPairElaboration, GateInstancePullPairIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire o, i;\n"
      "  buf (pull0, pull1) b1 (o, i);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StrengthPairElaboration, GateInstanceWeakPairIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire o, i;\n"
      "  buf (weak0, weak1) b1 (o, i);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// Continuous assignment is the other grammar position that carries driving
// strength. A drive strength on a continuous assign must elaborate cleanly —
// this is the positive counterpart to the illegal-pair cases above.
TEST(StrengthPairElaboration, ContAssignStrongPairIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, strong1) w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// Charge storage strengths (small, medium, large) belong exclusively to the
// trireg net type. Applying one to a plain wire must be rejected.
TEST(ChargeStrengthElaboration, SmallOnNonTriregIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (small) w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ChargeStrengthElaboration, MediumOnNonTriregIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (medium) w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ChargeStrengthElaboration, LargeOnNonTriregIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (large) w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// The same three charge storage strengths are legal on a trireg net, which is
// the only net type for which they are defined to originate.
TEST(ChargeStrengthElaboration, SmallOnTriregIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  trireg (small) t;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChargeStrengthElaboration, MediumOnTriregIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  trireg (medium) t;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ChargeStrengthElaboration, LargeOnTriregIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  trireg (large) t;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
