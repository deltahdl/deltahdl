#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- Property declarations elaborate without errors ---

TEST(AssertionDeclElaboration, PropertyDeclElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property p;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, PropertyDeclWithPortsElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property p(x, y);\n"
      "    x |-> y;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- Sequence declarations elaborate without errors ---

TEST(AssertionDeclElaboration, SequenceDeclElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, SequenceDeclWithPortsElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  sequence s(x, y);\n"
      "    x ##1 y;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- Concurrent assertion statements elaborate without errors ---

TEST(AssertionDeclElaboration, AssertPropertyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, AssumePropertyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  assume property (@(posedge clk) a |-> b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, CoverPropertyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  cover property (@(posedge clk) a |-> b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, CoverSequenceElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  cover sequence (@(posedge clk) a ##1 b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, RestrictPropertyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  restrict property (@(posedge clk) a |-> b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- Combined declarations and assertions elaborate ---

TEST(AssertionDeclElaboration, PropertyDeclWithAssertElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property p;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  assert property (p);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, SequenceDeclWithCoverElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  cover sequence (s);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, PropertyAndSequenceDeclsTogether) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property p; a; endproperty\n"
      "  sequence s; b; endsequence\n"
      "  assert property (p);\n"
      "  cover sequence (s);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, AllFiveConcurrentAssertionsElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  assert property (@(posedge clk) a);\n"
      "  assume property (@(posedge clk) b);\n"
      "  cover property (@(posedge clk) c);\n"
      "  cover sequence (@(posedge clk) d);\n"
      "  restrict property (@(posedge clk) e);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- Assertion with disable iff elaborates ---

TEST(AssertionDeclElaboration, AssertPropertyWithDisableIffElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) disable iff (rst) a |-> b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- Named assertion elaborates ---

TEST(AssertionDeclElaboration, NamedAssertPropertyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  my_assert: assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
