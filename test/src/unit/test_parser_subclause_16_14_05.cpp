#include <string>
#include <vector>

#include "fixture_parser.h"

using namespace delta;

namespace {

// The kinds of the items of the one module of `src`, in order.
std::vector<ModuleItemKind> ItemKinds(const std::string& src) {
  auto r = Parse(src);
  std::vector<ModuleItemKind> kinds;
  if (r.cu == nullptr || r.cu->modules.size() != 1) return kinds;
  for (auto* item : r.cu->modules[0]->items) kinds.push_back(item->kind);
  return kinds;
}

// §16.14.5: assert property (ps) action_block is equivalent to always assert
// property (ps) action_block ; and cover property (ps) statement_or_null to
// always cover property (ps) statement_or_null, so the always form is read
// as the concurrent assertion item the bare form is, the `;` the assert
// form ends with being a null item, and an assume, a cover sequence and a
// restrict under always are read the same.
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

// §16.14.5 names the concurrent assertion statements alone: an always
// procedure whose body is an immediate assertion, a deferred one or a
// statement other than an assertion is the procedure it is written as.
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
