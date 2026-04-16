#include "fixture_elaborator.h"

namespace {

// --- Req 1: Extern declaration coexists with actual definition ---

TEST(ExternModuleElaboration, ExternDeclarationSkippedForInstantiation) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern module child(input logic a, output logic b);\n"
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top(input logic a, output logic b);\n"
      "  child u0(.a(a), .b(b));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* child = top->children[0].resolved;
  ASSERT_NE(child, nullptr);
  EXPECT_FALSE(child->assigns.empty());
}

TEST(ExternModuleElaboration, ExternDeclarationDoesNotDuplicatePorts) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern module m(input logic a, output logic b);\n"
      "module m(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  EXPECT_EQ(top->ports.size(), 2u);
  EXPECT_FALSE(top->assigns.empty());
}

// --- Req 2: .* port resolution from extern declaration ---

TEST(ExternModuleElaboration, WildcardPortsResolvedFromExtern) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern module m(input logic a, output logic b);\n"
      "module m(.*);\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->ports.size(), 2u);
  EXPECT_FALSE(top->assigns.empty());
}

TEST(ExternModuleElaboration, WildcardPortsResolveDirections) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern module m(input logic a, output logic b);\n"
      "module m(.*);\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->ports.size(), 2u);
  EXPECT_EQ(top->ports[0].direction, Direction::kInput);
  EXPECT_EQ(top->ports[1].direction, Direction::kOutput);
}

TEST(ExternModuleElaboration, WildcardPortsWithParametersFromExtern) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern module m #(parameter W = 8)\n"
      "  (input logic [W-1:0] a, output logic [W-1:0] b);\n"
      "module m(.*);\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  EXPECT_FALSE(top->params.empty());
  ASSERT_EQ(top->ports.size(), 2u);
}

TEST(ExternModuleElaboration, WildcardModuleInstantiatedFromParent) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern module child(input logic [7:0] a, output logic [7:0] b);\n"
      "module child(.*);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  child u0(.a(a), .b(b));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  auto* child = top->children[0].resolved;
  ASSERT_NE(child, nullptr);
  EXPECT_EQ(child->ports.size(), 2u);
}

// --- Req 4: Extern shall match actual definition ---

TEST(ExternModuleElaboration, MatchingPortsNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern module m(input logic a, output logic b);\n"
      "module m(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExternModuleElaboration, PortCountMismatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "extern module m(input logic a, output logic b);\n"
      "module m(input logic a);\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(ExternModuleElaboration, PortNameMismatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "extern module m(input logic a, output logic b);\n"
      "module m(input logic x, output logic y);\n"
      "  assign y = x;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(ExternModuleElaboration, ParamCountMismatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "extern module m #(parameter W = 8)\n"
      "  (input logic a, output logic b);\n"
      "module m(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
