#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ParseResult3_11 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult3_11 Parse(const std::string& src) {
  ParseResult3_11 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FindItemByKind(ParseResult3_11& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

// =============================================================================
// LRM section 3.11 -- Overview of hierarchy
// =============================================================================

// §3.11: "Hierarchy is created by one building block instantiating another."
//        "Primitives cannot instantiate other building blocks; they are
//        leaves." "SystemVerilog permits multiple top-level blocks."
TEST(ParserSection3, Sec3_11_HierarchyAndInstantiation) {
  auto r = Parse(
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
  int gates = 0;
  for (const auto* item : r.cu->modules[1]->items)
    if (item->kind == ModuleItemKind::kGateInst) ++gates;
  EXPECT_EQ(gates, 4);
}
