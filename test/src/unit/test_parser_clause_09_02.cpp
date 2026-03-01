// §9.2: Structured procedures

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

static std::vector<ModuleItem*> FindUdpInsts(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> insts;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kUdpInst) insts.push_back(item);
  }
  return insts;
}

static std::vector<ModuleItem*> FindContAssigns(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kContAssign) result.push_back(item);
  }
  return result;
}

static std::vector<ModuleItem*> FindItems(const std::vector<ModuleItem*>& items,
                                          ModuleItemKind kind) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == kind) result.push_back(item);
  }
  return result;
}

namespace {

TEST(ParserA602, InitialConstruct_Multiple) {
  // Multiple initial blocks in the same module
  auto r = Parse(
      "module m;\n"
      "  initial a = 0;\n"
      "  initial b = 0;\n"
      "  initial c = 0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto inits =
      FindItems(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  EXPECT_EQ(inits.size(), 3u);
}

struct ParseResult9c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9c Parse(const std::string& src) {
  ParseResult9c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// §9.2 -- Structured procedures (initial, always, final)
// =============================================================================
TEST(ParserSection9b, StructuredProcInitialAndAlways) {
  auto r = Parse(
      "module m;\n"
      "  initial a = 0;\n"
      "  always #5 clk = ~clk;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
  EXPECT_EQ(r.cu->modules[0]->items[1]->kind, ModuleItemKind::kAlwaysBlock);
}

}  // namespace
