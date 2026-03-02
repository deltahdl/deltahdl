// §16.5.2: Assertion clock

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

// --- F.16: Negedge clocking ---
TEST(ParserAnnexF, AnnexFNegedgeClocking) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(negedge clk) a |-> ##1 b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

}  // namespace
