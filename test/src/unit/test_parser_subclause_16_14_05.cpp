#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_parser.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

std::vector<ModuleItemKind> ItemKinds(const std::string& src) {
  auto r = Parse(src);
  std::vector<ModuleItemKind> kinds;
  if (r.cu == nullptr || r.cu->modules.size() != 1) return kinds;
  for (auto* item : r.cu->modules[0]->items) kinds.push_back(item->kind);
  return kinds;
}

TEST(StaticConcurrentAssertionParsing, TheAlwaysFormIsTheBareStatement) {
  EXPECT_EQ(
      ItemKinds("module m;\n"
                "  always assert property (@(posedge clk) a |-> b)\n"
                "    x++; else y++;;\n"
                "  always cover property (@(posedge clk) a |-> b)\n"
                "    x++;\n"
                "  always assume property (@(posedge clk) a);\n"
                "  always cover sequence (@(posedge clk) a ##1 b);\n"
                "  always restrict property (@(posedge clk) a);\n"
                "endmodule\n"),
      std::vector<ModuleItemKind>(
          {ModuleItemKind::kAssertProperty, ModuleItemKind::kCoverProperty,
           ModuleItemKind::kAssumeProperty, ModuleItemKind::kCoverSequence,
           ModuleItemKind::kRestrictProperty}));
}

TEST(StaticConcurrentAssertionParsing, AnAlwaysProcedureStaysAProcedure) {
  EXPECT_EQ(
      ItemKinds("module m;\n"
                "  always assert (a) x++;\n"
                "  always assert #0 (a) x++;\n"
                "  always @(posedge clk) assert property (a) x++;\n"
                "  always_ff @(posedge clk) x++;\n"
                "endmodule\n"),
      std::vector<ModuleItemKind>(
          {ModuleItemKind::kAlwaysBlock, ModuleItemKind::kAlwaysBlock,
           ModuleItemKind::kAlwaysBlock, ModuleItemKind::kAlwaysFFBlock}));
}

}  // namespace
