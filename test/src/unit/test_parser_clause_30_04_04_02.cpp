#include "fixture_parser.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SimpleStateDependentPathParsing, ParallelPath) {
  auto sp = ParseSpecifySingle(
      "module m(input a, en, output b);\n"
      "  specify\n"
      "    if (en) (a => b) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_NE(si->path.condition, nullptr);
  EXPECT_FALSE(si->path.is_ifnone);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0].name, "b");
  ASSERT_EQ(si->path.delays.size(), 1u);
}

TEST(SimpleStateDependentPathParsing, FullPath) {
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

// The `+` polarity operator belongs to the simple path grammar, so it must
// remain usable underneath the `if (cond)` wrapper.
TEST(SimpleStateDependentPathParsing, ParallelPathWithPolarity) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (sel) (a + => b) = 8;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.condition, nullptr);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kPositive);
}

// The subclause explicitly allows several simple state-dependent paths to
// coexist in one specify block so that each condition contributes its own
// delay. The parser must accept the whole list without merging or rejecting
// later entries.
TEST(SimpleStateDependentPathParsing, MultipleCoexistingPaths) {
  auto r = Parse(
      "module m(input a, b, output y);\n"
      "  specify\n"
      "    if (a) (a => y) = 1;\n"
      "    if (b) (a => y) = 2;\n"
      "    if (!a && !b) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Parallel and full simple state-dependent paths should be mixable in the
// same specify block since the subclause names both as legal descriptions.
TEST(SimpleStateDependentPathParsing, MixedParallelAndFullCoexist) {
  auto r = Parse(
      "module m(input a, b, output y);\n"
      "  specify\n"
      "    if (a) (a => y) = 1;\n"
      "    if (b) (a, b *> y) = 2;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
