// §28.11

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §28.11 R4: the (highz0, highz1) pair is rejected regardless of which host
// construct carries the strength spec. Gate-instance coverage complements the
// continuous-assign tests in §10.3.4.
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

TEST(StrengthPairElaboration, GateInstanceStrong0WithHighz1IsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire o, i;\n"
      "  buf (strong0, highz1) b1 (o, i);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// A fully specified non-highz pair must elaborate without any strength-related
// complaint on either a gate instance or a net declaration.
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

TEST(StrengthPairElaboration, NetDeclPullPairIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (pull0, pull1) w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
