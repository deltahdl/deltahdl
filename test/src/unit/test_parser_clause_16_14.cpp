// §16.14: Concurrent assertions

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;
static size_t CountItemsByKind(const std::vector<ModuleItem*>& items,
                               ModuleItemKind kind) {
  size_t count = 0;
  for (auto* item : items) {
    if (item->kind == kind) ++count;
  }
  return count;
}

using VerifyParseTest = ProgramTestParse;

namespace {

// =============================================================================
// Section 16.5.1 -- Multiple concurrent assertions in same module
// =============================================================================
// Multiple assert/assume/cover property items in one module.
TEST(ParserSection16, Sec16_5_1_MultipleConcurrentAssertions) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "  assume property (@(posedge clk) en);\n"
      "  cover property (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(CountItemsByKind(r.cu->modules[0]->items,
                             ModuleItemKind::kAssertProperty),
            1u);
  EXPECT_EQ(CountItemsByKind(r.cu->modules[0]->items,
                             ModuleItemKind::kAssumeProperty),
            1u);
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty),
      1u);
}

}  // namespace
