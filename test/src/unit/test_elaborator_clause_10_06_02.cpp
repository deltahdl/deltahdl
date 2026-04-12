#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "fixture_elaborator.h"
#include "helpers_force_target.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;
namespace {

TEST(ForceReleaseElaboration, VarLvalueForceReleaseElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial begin force x = 1; release x; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  initial begin force w = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceConcatLhsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin force {a, b} = 2'b11; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceConstBitSelectNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "  initial begin force bus[3] = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceReleaseElaboration, ForceConstPartSelectNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "  initial begin force bus[7:4] = 4'hF; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ForceRelease, LegalTargetNet) {
  ForceInfo info{ForceTarget::kNet};
  EXPECT_TRUE(ValidateForceTarget(info));
}

TEST(ForceRelease, LegalTargetConcatenation) {
  ForceInfo info{ForceTarget::kConcatenation};
  EXPECT_TRUE(ValidateForceTarget(info));
}

TEST(ForceRelease, IllegalBitSelectVariable) {
  ForceInfo info{ForceTarget::kBitSelectVariable};
  EXPECT_FALSE(ValidateForceTarget(info));
}

TEST(ForceRelease, IllegalPartSelectVariable) {
  ForceInfo info{ForceTarget::kPartSelectVariable};
  EXPECT_FALSE(ValidateForceTarget(info));
}

TEST(ForceRelease, IllegalMixedAssignmentTarget) {
  ForceInfo info{ForceTarget::kSingularVariable};
  info.has_mixed_assignments = true;
  EXPECT_FALSE(ValidateForceTarget(info));
}

}  // namespace
