#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ParseResult312 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult312 Parse(const std::string &src) {
  ParseResult312 result;
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

static const ModuleItem *
FindInstByModule(const std::vector<ModuleItem *> &items,
                 const std::string &module_name) {
  for (const auto *item : items)
    if (item->kind == ModuleItemKind::kModuleInst &&
        item->inst_module == module_name)
      return item;
  return nullptr;
}

// =============================================================================
// LRM §3.12 — Compilation and elaboration
// =============================================================================

// §3.12 Compilation and elaboration with parameterized instantiation
TEST(ParserClause03, Cl3_12_CompilationAndElaboration) {
  auto r = Parse("package pkg; typedef logic [7:0] byte_t; endpackage\n"
                 "module adder #(parameter W = 8) (\n"
                 "    input [W-1:0] a, b, output [W-1:0] s);\n"
                 "  assign s = a + b;\n"
                 "endmodule\n"
                 "module top; import pkg::*;\n"
                 "  wire [15:0] x, y, z;\n"
                 "  adder #(16) u0 (.a(x), .b(y), .s(z));\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // Package compiled before module references it
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  // Parameterized module: elaboration computes parameter values
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->params.size(), 1u);
  // Elaboration expands instantiation with parameter override & connectivity
  const auto *inst = FindInstByModule(r.cu->modules[1]->items, "adder");
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_params.size(), 1u);
  EXPECT_EQ(inst->inst_ports.size(), 3u);
}
