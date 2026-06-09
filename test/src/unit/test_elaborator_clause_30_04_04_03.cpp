#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(EdgeSensitiveStateDependentPathElaboration, FullPathWithDataSourceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (en) (posedge clk *> (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(EdgeSensitiveStateDependentPathElaboration, CoexistingUniqueByEdgeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (c) (posedge clk => q) = 1;\n"
      "    if (c) (negedge clk => q) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.4.3 criterion: the same edge-sensitive path may carry different delays
// only when every port is referenced the same way in each declaration. Here the
// destination is a part-select in one declaration and a bit-select in the other,
// which is illegal (LRM Example 4).
TEST(EdgeSensitiveStateDependentPathElaboration, InconsistentPortReferenceIsIllegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input reset, output [3:0] q);\n"
      "  reg [3:0] data;\n"
      "  specify\n"
      "    if (reset) (posedge clk => (q[3:0] : data)) = (10, 5);\n"
      "    if (!reset) (posedge clk => (q[0] : data)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// Criterion 2 also distinguishes "entire port" as a reference style: referencing
// the whole port in one declaration and a select in another for the same path is
// likewise illegal (exercises the entire-port branch of the consistency check).
TEST(EdgeSensitiveStateDependentPathElaboration, EntirePortVsBitSelectIsIllegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input reset, output [3:0] q);\n"
      "  reg [3:0] data;\n"
      "  specify\n"
      "    if (reset) (posedge clk => (q : data)) = (10, 5);\n"
      "    if (!reset) (posedge clk => (q[0] : data)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// Criterion 2 applies to every port on the path, not just the destination.
// Here the destination is referenced consistently (whole port) but the edge
// source is a part-select in one declaration and a bit-select in the other,
// which is illegal (exercises the source-side branch of the consistency check).
TEST(EdgeSensitiveStateDependentPathElaboration, InconsistentSourceReferenceIsIllegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [3:0] clk, input reset, output q);\n"
      "  reg data;\n"
      "  specify\n"
      "    if (reset) (posedge clk[3:0] => (q : data)) = (10, 5);\n"
      "    if (!reset) (posedge clk[0] => (q : data)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// Positive control: identical reference style across declarations is accepted,
// confirming the consistency check above does not reject matching part-selects.
TEST(EdgeSensitiveStateDependentPathElaboration, ConsistentPartSelectReferenceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input reset, output [3:0] q);\n"
      "  reg [3:0] data;\n"
      "  specify\n"
      "    if (reset) (posedge clk => (q[3:0] : data)) = (10, 5);\n"
      "    if (!reset) (posedge clk => (q[3:0] : data)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}
