// §30.4.4.2: Simple state-dependent paths

#include "fixture_parser.h"

using namespace delta;

namespace {

// if (expr) simple_path_declaration — full
TEST(ParserA702, StateDependentIfSimpleFull) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (en) (a, b *> c) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.condition, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
}

}  // namespace
