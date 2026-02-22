#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ParseResult307 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult307 Parse(const std::string &src) {
  ParseResult307 result;
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

static int CountItemsByKind(const std::vector<ModuleItem *> &items,
                            ModuleItemKind kind) {
  int count = 0;
  for (const auto *item : items)
    if (item->kind == kind)
      ++count;
  return count;
}

static bool HasGateOfKind(const std::vector<ModuleItem *> &items,
                          GateKind kind) {
  for (const auto *item : items)
    if (item->kind == ModuleItemKind::kGateInst && item->gate_kind == kind)
      return true;
  return false;
}

// =============================================================================
// LRM §3.7 — Primitives
// =============================================================================

// §3.7: "SystemVerilog includes a number of built-in primitive types"
//       — logic gates and switches instantiated inside a module.
TEST(ParserClause03, Cl3_7_BuiltInPrimitives) {
  auto r = Parse("module gate_test(input a, b, c, output w, x, y, z);\n"
                 "  and g1(w, a, b);\n"
                 "  nand g2(x, a, b, c);\n"
                 "  bufif0 g3(y, a, b);\n"
                 "  nmos g4(z, a, b);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kGateInst), 4);
  EXPECT_TRUE(HasGateOfKind(r.cu->modules[0]->items, GateKind::kAnd));
  EXPECT_TRUE(HasGateOfKind(r.cu->modules[0]->items, GateKind::kNand));
  EXPECT_TRUE(HasGateOfKind(r.cu->modules[0]->items, GateKind::kBufif0));
  EXPECT_TRUE(HasGateOfKind(r.cu->modules[0]->items, GateKind::kNmos));
}

// §3.7: "Designers can supplement the built-in primitives with user-defined
//        primitives (UDPs). A UDP is enclosed between the keywords
//        primitive...endprimitive."
//        Combinational UDP with truth table for gate-level modeling.
TEST(ParserClause03, Cl3_7_CombinationalUdp) {
  auto r = Parse("primitive udp_or (output out, input a, b);\n"
                 "  table\n"
                 "    0 0 : 0;\n"
                 "    0 1 : 1;\n"
                 "    1 0 : 1;\n"
                 "    1 1 : 1;\n"
                 "  endtable\n"
                 "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  const auto *udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "udp_or");
  EXPECT_EQ(udp->output_name, "out");
  ASSERT_EQ(udp->input_names.size(), 2u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_FALSE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 4u);
  EXPECT_EQ(udp->table[0].output, '0');
  EXPECT_EQ(udp->table[3].output, '1');
}

// §3.7: Sequential UDP with initial statement — timing-accurate modeling
//        for sequential gate-level circuits.
TEST(ParserClause03, Cl3_7_SequentialUdp) {
  auto r = Parse("primitive udp_latch (output reg q, input d, en);\n"
                 "  initial q = 0;\n"
                 "  table\n"
                 "    1 1 : ? : 1;\n"
                 "    0 1 : ? : 0;\n"
                 "    ? 0 : ? : -;\n"
                 "  endtable\n"
                 "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  const auto *udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "udp_latch");
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');
  ASSERT_EQ(udp->table.size(), 3u);
  // Sequential rows have current_state field
  EXPECT_EQ(udp->table[0].current_state, '?');
  EXPECT_EQ(udp->table[0].output, '1');
  EXPECT_EQ(udp->table[2].output, '-');
}
