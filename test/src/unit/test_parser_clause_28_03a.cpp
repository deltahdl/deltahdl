// Tests for §28.3 — Gate and switch declaration syntax

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static void VerifyGateInstances(const std::vector<ModuleItem *> &items,
                                GateKind kind,
                                const std::string expected_names[],
                                size_t count) {
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(items[i]->gate_kind, kind);
    EXPECT_EQ(items[i]->gate_inst_name, expected_names[i]);
    EXPECT_EQ(items[i]->gate_terminals.size(), 3);
  }
}

static void VerifyStrengthDelayInstances(const std::vector<ModuleItem *> &items,
                                         size_t count, int str0, int str1) {
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(items[i]->drive_strength0, str0);
    EXPECT_EQ(items[i]->drive_strength1, str1);
    EXPECT_NE(items[i]->gate_delay, nullptr);
  }
}

TEST(ParserSection28, MultipleInstances) {
  auto r = Parse("module m;\n"
                 "  and g1(a, b, c), g2(d, e, f);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  std::string expected_names[] = {"g1", "g2"};
  VerifyGateInstances(mod->items, GateKind::kAnd, expected_names, 2);
}

TEST(ParserSection28, MultipleInstancesThree) {
  auto r = Parse("module m;\n"
                 "  nand n1(a, b, c), n2(d, e, f), n3(g, h, i);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 3);
  EXPECT_EQ(mod->items[0]->gate_inst_name, "n1");
  EXPECT_EQ(mod->items[1]->gate_inst_name, "n2");
  EXPECT_EQ(mod->items[2]->gate_inst_name, "n3");
}

TEST(ParserSection28, MultipleInstancesNoNames) {
  auto r = Parse("module m;\n"
                 "  or (a, b, c), (d, e, f);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  EXPECT_TRUE(mod->items[0]->gate_inst_name.empty());
  EXPECT_TRUE(mod->items[1]->gate_inst_name.empty());
}

TEST(ParserSection28, MultipleInstancesWithStrengthAndDelay) {
  auto r = Parse("module m;\n"
                 "  and (strong0, strong1) #5 g1(a, b, c), g2(d, e, f);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  VerifyStrengthDelayInstances(mod->items, 2, 4, 4);
}

TEST(ParserSection28, StrengthWithDelay) {
  auto r = Parse("module m;\n"
                 "  and (strong0, strong1) #5 g1(out, a, b);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 4); // strong0
  EXPECT_EQ(item->drive_strength1, 4); // strong1
  EXPECT_NE(item->gate_delay, nullptr);
  ASSERT_EQ(item->gate_terminals.size(), 3);
}
