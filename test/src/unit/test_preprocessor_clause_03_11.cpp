// §3.11: Overview of hierarchy

#include "fixture_parser.h"

using namespace delta;

static ModuleItem* FindItemByKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

namespace {

// =============================================================================
// LRM §3.11 — Overview of hierarchy
// =============================================================================
// §3.11 Hierarchy through instantiation, primitives as leaves, multiple tops
TEST(ParserClause03, Cl3_11_HierarchyAndInstantiation) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  logic in1, in2, sel;\n"
      "  wire out1;\n"
      "  mux2to1 m1 (.a(in1), .b(in2), .sel(sel), .y(out1));\n"
      "endmodule\n"
      "module mux2to1 (input wire a, b, sel, output logic y);\n"
      "  not g1 (sel_n, sel);\n"
      "  and g2 (a_s, a, sel_n);\n"
      "  and g3 (b_s, b, sel);\n"
      "  or  g4 (y, a_s, b_s);\n"
      "endmodule : mux2to1\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // Multiple top-level blocks
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->name, "top");
  EXPECT_EQ(r.cu->modules[1]->name, "mux2to1");
  // Hierarchy through instantiation with port connections for communication
  auto* inst = FindItemByKind(r, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_module, "mux2to1");
  EXPECT_EQ(inst->inst_name, "m1");
  EXPECT_EQ(inst->inst_ports.size(), 4u);
  // Primitives as leaves: gate primitives (not, and, or)
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[1]->items, ModuleItemKind::kGateInst), 4);
}

}  // namespace
