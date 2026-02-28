// §30.4.6: Declaring multiple module paths in a single statement

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserAnnexA, A7SpecifyFullPath) {
  auto r =
      Parse("module m; specify (a, b *> c, d) = 10; endspecify endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.7.3 list_of_path_inputs / list_of_path_outputs
// =============================================================================
// list_of_path_inputs — multiple simple input terminals
TEST(ParserA703, ListOfPathInputsMultiple) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a, b, c => d) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.src_ports.size(), 3u);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  EXPECT_EQ(si->path.src_ports[1].name, "b");
  EXPECT_EQ(si->path.src_ports[2].name, "c");
}

}  // namespace
