#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- list_of_variable_decl_assignments elaboration ---

TEST(DeclarationListElaboration, MultipleVariablesElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic a, b, c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 3u);
}

TEST(DeclarationListElaboration, MultipleNetsElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->nets.size(), 3u);
}

// --- list_of_param_assignments elaboration ---

TEST(DeclarationListElaboration, MultipleParamsElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter A = 1, B = 2, C = 3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  int count = 0;
  for (auto& p : mod->params) {
    if (p.name == "A" || p.name == "B" || p.name == "C") count++;
  }
  EXPECT_EQ(count, 3);
}

// --- list_of_genvar_identifiers elaboration ---

TEST(DeclarationListElaboration, MultipleGenvarsElaborate) {
  EXPECT_TRUE(ElabOk("module m; genvar i, j; endmodule"));
}

// --- list_of_port_identifiers elaboration ---

TEST(DeclarationListElaboration, MultiplePortsElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic a, input logic b, output logic c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->ports.size(), 3u);
}

// --- list_of_type_assignments elaboration ---

TEST(DeclarationListElaboration, TypeParamsElaborate) {
  EXPECT_TRUE(ElabOk(
      "module m; parameter type T1 = int, T2 = real; endmodule"));
}

}  // namespace
