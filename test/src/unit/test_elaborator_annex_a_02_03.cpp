#include "fixture_elaborator.h"

using namespace delta;

namespace {

// The §6.8 "set of variables sharing the same characteristics, declared in
// the same declaration statement" rule is tested at the elaborator stage in
// test_elaborator_clause_06_08.cpp (MultipleVarsInOneStatement). The
// corresponding test previously duplicated in this file has been removed.

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
