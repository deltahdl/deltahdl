// §16.12.5: Conjunction property

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

namespace {

// --- F.11: Property and ---
TEST(ParserAnnexF, AnnexFPropertyAnd) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) (a |-> b) and (c |-> d));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

}  // namespace
