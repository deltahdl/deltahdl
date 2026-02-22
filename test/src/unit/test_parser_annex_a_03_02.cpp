#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem *FindGateByKind(const std::vector<ModuleItem *> &items,
                                  GateKind kind) {
  for (auto *item : items) {
    if (item->kind == ModuleItemKind::kGateInst && item->gate_kind == kind)
      return item;
  }
  return nullptr;
}

static std::vector<ModuleItem *>
FindAllGates(const std::vector<ModuleItem *> &items) {
  std::vector<ModuleItem *> gates;
  for (auto *item : items) {
    if (item->kind == ModuleItemKind::kGateInst)
      gates.push_back(item);
  }
  return gates;
}

} // namespace

// =============================================================================
// A.3.2 Primitive strengths
//
// pulldown_strength ::=
//   ( strength0 , strength1 )
//   | ( strength1 , strength0 )
//   | ( strength0 )
//
// pullup_strength ::=
//   ( strength0 , strength1 )
//   | ( strength1 , strength0 )
//   | ( strength1 )
// =============================================================================

// -----------------------------------------------------------------------------
// Production #1: pulldown_strength
// pulldown_strength ::= ( strength0 , strength1 )
// -----------------------------------------------------------------------------

TEST(ParserA302, PulldownStrength_Strength0Strength1) {
  auto r = Parse("module m;\n"
                 "  pulldown (strong0, pull1) pd1(out);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u); // strong0
  EXPECT_EQ(g->drive_strength1, 3u); // pull1
  EXPECT_EQ(g->gate_inst_name, "pd1");
}

TEST(ParserA302, PulldownStrength_Supply0Weak1) {
  auto r = Parse("module m;\n"
                 "  pulldown (supply0, weak1) (out);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 5u); // supply0
  EXPECT_EQ(g->drive_strength1, 2u); // weak1
}

TEST(ParserA302, PulldownStrength_Pull0Highz1) {
  auto r = Parse("module m;\n"
                 "  pulldown (pull0, highz1) pd1(out);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 3u); // pull0
  EXPECT_EQ(g->drive_strength1, 1u); // highz1
}

// -----------------------------------------------------------------------------
// Production #1: pulldown_strength
// pulldown_strength ::= ( strength1 , strength0 )
// -----------------------------------------------------------------------------

TEST(ParserA302, PulldownStrength_Strength1Strength0) {
  auto r = Parse("module m;\n"
                 "  pulldown (pull1, strong0) pd1(out);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u); // strong0
  EXPECT_EQ(g->drive_strength1, 3u); // pull1
}

TEST(ParserA302, PulldownStrength_Highz1Supply0) {
  auto r = Parse("module m;\n"
                 "  pulldown (highz1, supply0) (out);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 5u); // supply0
  EXPECT_EQ(g->drive_strength1, 1u); // highz1
}

// -----------------------------------------------------------------------------
// Production #1: pulldown_strength
// pulldown_strength ::= ( strength0 )
// -----------------------------------------------------------------------------

TEST(ParserA302, PulldownStrength_SingleStrength0) {
  auto r = Parse("module m;\n"
                 "  pulldown (strong0) pd1(out);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u); // strong0
  EXPECT_EQ(g->drive_strength1, 0u); // none
}

TEST(ParserA302, PulldownStrength_SingleSupply0) {
  auto r = Parse("module m;\n"
                 "  pulldown (supply0) (out);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 5u); // supply0
  EXPECT_EQ(g->drive_strength1, 0u); // none
}

TEST(ParserA302, PulldownStrength_SingleWeak0) {
  auto r = Parse("module m;\n"
                 "  pulldown (weak0) pd1(out);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 2u); // weak0
  EXPECT_EQ(g->drive_strength1, 0u); // none
}

TEST(ParserA302, PulldownStrength_SinglePull0) {
  auto r = Parse("module m;\n"
                 "  pulldown (pull0) pd1(out);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 3u); // pull0
  EXPECT_EQ(g->drive_strength1, 0u); // none
}

TEST(ParserA302, PulldownStrength_SingleHighz0) {
  auto r = Parse("module m;\n"
                 "  pulldown (highz0) pd1(out);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 1u); // highz0
  EXPECT_EQ(g->drive_strength1, 0u); // none
}

// -----------------------------------------------------------------------------
// Production #2: pullup_strength
// pullup_strength ::= ( strength0 , strength1 )
// -----------------------------------------------------------------------------

TEST(ParserA302, PullupStrength_Strength0Strength1) {
  auto r = Parse("module m;\n"
                 "  pullup (strong0, pull1) pu1(out);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u); // strong0
  EXPECT_EQ(g->drive_strength1, 3u); // pull1
  EXPECT_EQ(g->gate_inst_name, "pu1");
}

TEST(ParserA302, PullupStrength_Weak0Supply1) {
  auto r = Parse("module m;\n"
                 "  pullup (weak0, supply1) (out);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 2u); // weak0
  EXPECT_EQ(g->drive_strength1, 5u); // supply1
}

// -----------------------------------------------------------------------------
// Production #2: pullup_strength
// pullup_strength ::= ( strength1 , strength0 )
// -----------------------------------------------------------------------------

TEST(ParserA302, PullupStrength_Strength1Strength0) {
  auto r = Parse("module m;\n"
                 "  pullup (supply1, weak0) pu1(out);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 2u); // weak0
  EXPECT_EQ(g->drive_strength1, 5u); // supply1
}

TEST(ParserA302, PullupStrength_Highz1Strong0) {
  auto r = Parse("module m;\n"
                 "  pullup (highz1, strong0) (out);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u); // strong0
  EXPECT_EQ(g->drive_strength1, 1u); // highz1
}

// -----------------------------------------------------------------------------
// Production #2: pullup_strength
// pullup_strength ::= ( strength1 )
// -----------------------------------------------------------------------------

TEST(ParserA302, PullupStrength_SingleStrength1) {
  auto r = Parse("module m;\n"
                 "  pullup (strong1) pu1(out);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u); // none
  EXPECT_EQ(g->drive_strength1, 4u); // strong1
}

TEST(ParserA302, PullupStrength_SingleSupply1) {
  auto r = Parse("module m;\n"
                 "  pullup (supply1) (out);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u); // none
  EXPECT_EQ(g->drive_strength1, 5u); // supply1
}

TEST(ParserA302, PullupStrength_SingleWeak1) {
  auto r = Parse("module m;\n"
                 "  pullup (weak1) pu1(out);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u); // none
  EXPECT_EQ(g->drive_strength1, 2u); // weak1
}

TEST(ParserA302, PullupStrength_SinglePull1) {
  auto r = Parse("module m;\n"
                 "  pullup (pull1) pu1(out);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u); // none
  EXPECT_EQ(g->drive_strength1, 3u); // pull1
}

TEST(ParserA302, PullupStrength_SingleHighz1) {
  auto r = Parse("module m;\n"
                 "  pullup (highz1) pu1(out);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u); // none
  EXPECT_EQ(g->drive_strength1, 1u); // highz1
}

// -----------------------------------------------------------------------------
// Combination: strength with multiple instances
// -----------------------------------------------------------------------------

TEST(ParserA302, PulldownStrength_MultipleInstances) {
  auto r = Parse("module m;\n"
                 "  pulldown (strong0, weak1) pd1(a), pd2(b);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, 4u); // strong0
  EXPECT_EQ(gates[0]->drive_strength1, 2u); // weak1
  EXPECT_EQ(gates[1]->drive_strength0, 4u); // strong0
  EXPECT_EQ(gates[1]->drive_strength1, 2u); // weak1
}

TEST(ParserA302, PullupStrength_MultipleInstances) {
  auto r = Parse("module m;\n"
                 "  pullup (weak0, strong1) pu1(a), pu2(b);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, 2u); // weak0
  EXPECT_EQ(gates[0]->drive_strength1, 4u); // strong1
  EXPECT_EQ(gates[1]->drive_strength0, 2u); // weak0
  EXPECT_EQ(gates[1]->drive_strength1, 4u); // strong1
}

TEST(ParserA302, PulldownStrength_SingleStrength0_MultipleInstances) {
  auto r = Parse("module m;\n"
                 "  pulldown (pull0) pd1(a), pd2(b);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, 3u); // pull0
  EXPECT_EQ(gates[0]->drive_strength1, 0u); // none
  EXPECT_EQ(gates[1]->drive_strength0, 3u); // pull0
  EXPECT_EQ(gates[1]->drive_strength1, 0u); // none
}

TEST(ParserA302, PullupStrength_SingleStrength1_MultipleInstances) {
  auto r = Parse("module m;\n"
                 "  pullup (pull1) pu1(a), pu2(b);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, 0u); // none
  EXPECT_EQ(gates[0]->drive_strength1, 3u); // pull1
  EXPECT_EQ(gates[1]->drive_strength0, 0u); // none
  EXPECT_EQ(gates[1]->drive_strength1, 3u); // pull1
}

// -----------------------------------------------------------------------------
// All strength0 values exercised in pulldown_strength
// -----------------------------------------------------------------------------

TEST(ParserA302, PulldownStrength_AllStrength0Values) {
  // highz0=1, weak0=2, pull0=3, strong0=4, supply0=5
  EXPECT_TRUE(ParseOk("module m; pulldown (highz0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (weak0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (pull0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (strong0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (supply0) (out); endmodule"));
}

// -----------------------------------------------------------------------------
// All strength1 values exercised in pullup_strength
// -----------------------------------------------------------------------------

TEST(ParserA302, PullupStrength_AllStrength1Values) {
  // highz1=1, weak1=2, pull1=3, strong1=4, supply1=5
  EXPECT_TRUE(ParseOk("module m; pullup (highz1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (weak1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (pull1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (strong1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (supply1) (out); endmodule"));
}
