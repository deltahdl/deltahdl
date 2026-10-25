#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DriveStrengthElaboration, DriveStrengthOnVectorNetIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [7:0] w;\n"
      "  assign (strong0, weak1) w = 8'd0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength on continuous assignment applies only to scalar nets", 3,
      "10.3.4"));
}

TEST(DriveStrengthElaboration, DriveStrengthOnScalarNetIsValid) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, weak1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DriveStrengthElaboration, SupplyNetTypeHasNoStrengthError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  supply0 [7:0] s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DriveStrengthElaboration, DefaultStrengthIsZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_EQ(mod->assigns[0].drive_strength0, 0u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 0u);
}

TEST(DriveStrengthElaboration, NetDeclStrengthOnScalarIsValid) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (weak0, strong1) w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DriveStrengthElaboration, NetDeclStrengthOnVectorIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (weak0, strong1) [3:0] w = 4'd0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength on continuous assignment applies only to scalar nets", 2,
      "10.3.4"));
}

TEST(DriveStrengthElaboration, DriveStrengthOnScalarVariableIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic v;\n"
      "  assign (strong0, weak1) v = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength not allowed on continuous assignment to a variable", 3,
      "10.3.4"));
}

TEST(DriveStrengthElaboration, DriveStrengthPropagatedToImplicitContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire (supply0, strong1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 5u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 4u);
}

TEST(DriveStrengthElaboration, Supply1VectorNetTypeHasNoStrengthError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  supply1 [7:0] s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §10.3.4: the strength pairs (highz1, highz0) and (highz0, highz1) shall be
// treated as illegal constructs. The parser accepts the syntax (both slots
// encode to the highz level); the elaborator rejects an all-highz drive
// strength on a continuous assignment.
TEST(DriveStrengthElaboration, Highz0Highz1ContAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz0, highz1) w = 1'b0;\n"
      "endmodule\n",
      f);
  // The all-highz pair is reported under §28.3.2, which is where deltahdl
  // states the rule §10.3.4 also carries.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "drive strength (highz0, highz1) is illegal", 3,
                            "28.3.2"));
}

// The order of the two strengths is arbitrary, so the reversed all-highz pair
// is equally illegal.
TEST(DriveStrengthElaboration, Highz1Highz0ContAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz1, highz0) w = 1'b0;\n"
      "endmodule\n",
      f);
  // Reported under §28.3.2, as in Highz0Highz1ContAssignIsError.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "drive strength (highz0, highz1) is illegal", 3,
                            "28.3.2"));
}

// The same prohibition applies when the all-highz strength is written on a net
// declaration assignment.
TEST(DriveStrengthElaboration, Highz0Highz1NetDeclIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (highz0, highz1) w = 1'b0;\n"
      "endmodule\n",
      f);
  // Reported under §28.3.2, at the declarator name the net declaration's
  // ModuleItem stands at.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "drive strength (highz0, highz1) is illegal", 2,
                            "28.3.2"));
}

TEST(DriveStrengthElaboration, MultipleAssignsPreserveIndependentStrengths) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  assign (supply0, supply1) a = 1'b1;\n"
      "  assign (weak0, weak1) b = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 2u);
  EXPECT_EQ(mod->assigns[0].drive_strength0, 5u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 5u);
  EXPECT_EQ(mod->assigns[1].drive_strength0, 2u);
  EXPECT_EQ(mod->assigns[1].drive_strength1, 2u);
}

// §10.3.4 (printed page 251): a drive strength applies only to an assignment
// to a scalar net, and neither a select of a vector net nor a concatenation of
// nets is one; a supply net's select is excepted from those it applies to with
// the net, and is reported as a supply net.
TEST(DriveStrengthElaboration, DriveStrengthOnSelectOfVectorNetIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire [7:0] w; wire a, b; supply1 [3:0] s;\n"
      "  assign (weak0, weak1) w[3:0] = 4'h0;\n"
      "  assign (weak0, weak1) {a, b} = 2'b0;\n"
      "  assign (weak0, weak1) s[1:0] = 2'b0;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 4u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "drive strength on continuous assignment "
                              "applies only to scalar nets",
                              line, "10.3.4"));
  }
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "drive strength on continuous assignment does "
                            "not apply to supply0 or supply1 nets",
                            5, "10.3.4"));
}

// §10.3.4 (printed page 251): the nets of types supply0 and supply1 are
// excepted from the scalar nets a drive strength applies to, whatever their
// width, and whether the strength is written on an assign or on the net
// declaration assignment. The wire beside them keeps its strength.
TEST(DriveStrengthElaboration, DriveStrengthOnSupplyNetIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  supply1 [3:0] s; supply0 z; wire w;\n"
      "  assign (weak0, weak1) s = 4'h0;\n"
      "  assign (weak0, weak1) z = 1'b1;\n"
      "  supply1 (weak0, weak1) v = 1'b0;\n"
      "  assign (weak0, weak1) w = 1'b1;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 4u, 5u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "drive strength on continuous assignment does "
                              "not apply to supply0 or supply1 nets",
                              line, "10.3.4"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "drive strength on continuous assignment "
                             "applies only to scalar nets",
                             3, "10.3.4"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "drive strength on continuous assignment does "
                             "not apply to supply0 or supply1 nets",
                             6, "10.3.4"));
}

// §10.3.4 (printed page 251): a member of a net whose data type is a packed
// structure is part of a vector net, as a part-select is, so a drive strength
// on an assignment to it is reported as one on a select of a vector net. A net
// of an interface instance, reached through the instance's name, is the
// interface's, and this module's assignment to it leaves it unjudged.
TEST(DriveStrengthElaboration, DriveStrengthOnMemberOfStructureNetIsError) {
  ElabFixture f;
  Elaborate(
      "interface bus;\n"
      "  wire y;\n"
      "endinterface\n"
      "module m;\n"
      "  typedef struct packed { logic a; logic b; } s_t;\n"
      "  wire s_t n;\n"
      "  logic x;\n"
      "  bus b();\n"
      "  assign (weak0, weak1) n.a = x;\n"
      "  assign (weak0, weak1) b.y = x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength on continuous assignment applies only to scalar nets", 9,
      "10.3.4"));
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength on continuous assignment applies only to scalar nets", 10,
      "10.3.4"));
}

}  // namespace
