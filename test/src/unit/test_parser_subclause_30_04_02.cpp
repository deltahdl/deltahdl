#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_specify.h"

using namespace delta;

namespace {

TEST(SpecifyPathParsing, PathDeclSimpleParallel) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kNone);
  EXPECT_EQ(si->path.condition, nullptr);
  EXPECT_FALSE(si->path.is_ifnone);
}

TEST(SpecifyPathParsing, PathDeclSimpleFull) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a, b *> c) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  ASSERT_EQ(si->path.src_ports.size(), 2u);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
}

TEST(SpecifyPathParsing, ParallelPathRejectsMultipleSources) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a, b => c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "parallel path '=>' requires a single source and destination", 3,
      "30.4.5"));
}

TEST(SpecifyPathParsing, ParallelPathRejectsMultipleDestinations) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b, c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "parallel path '=>' requires a single source and destination", 3,
      "30.4.5"));
}

TEST(SpecifyPathParsing, InputTerminalBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a[3] => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].range_kind, SpecifyRangeKind::kBitSelect);
}

TEST(SpecifyPathParsing, OutputTerminalBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b[0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0].range_kind, SpecifyRangeKind::kBitSelect);
}

TEST(SpecifyPathParsing, InputTerminalPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a[7:0] => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].range_kind, SpecifyRangeKind::kPartSelect);
}

TEST(SpecifyPathParsing, OutputTerminalPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b[7:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0].range_kind, SpecifyRangeKind::kPartSelect);
}

TEST(SpecifyPathParsing, InputTerminalPlusIndexed) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a[0+:4] => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].range_kind, SpecifyRangeKind::kPlusIndexed);
}

TEST(SpecifyPathParsing, InputTerminalMinusIndexed) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a[3-:4] => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].range_kind, SpecifyRangeKind::kMinusIndexed);
}

TEST(SpecifyPathParsing, InterfacePortAsInputTerminal) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (intf.sig => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].interface_name, "intf");
  EXPECT_EQ(si->path.src_ports[0].name, "sig");
}

TEST(SpecifyPathParsing, InterfacePortAsOutputTerminal) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => intf.sig) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0].interface_name, "intf");
  EXPECT_EQ(si->path.dst_ports[0].name, "sig");
}

TEST(SpecifyPathParsing, FullPathPolarityWithMultipleSources) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a, b + *> c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kPositive);
  ASSERT_EQ(si->path.src_ports.size(), 2u);
}

TEST(SpecifyPathParsing, FullPathMultipleDestinations) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a *> b, c) = 7;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  ASSERT_EQ(si->path.dst_ports.size(), 2u);
  EXPECT_EQ(si->path.dst_ports[0].name, "b");
  EXPECT_EQ(si->path.dst_ports[1].name, "c");
}

TEST(SpecifyPathParsing, ParallelPathNegativePolarity) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a - => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kNegative);
}

TEST(SpecifyPathParsing, ParallelPathPositivePolarity) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a + => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kPositive);
}

TEST(SpecifyPathParsing, FullPathNegativePolarity) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a, b - *> c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kNegative);
}

TEST(SpecifyPathParsing, ParallelPathGluedPositivePolarity) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a +=> b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kPositive);
}

TEST(SpecifyPathParsing, ParallelPathGluedNegativePolarity) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a -=> b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kNegative);
}

TEST(SpecifyPathParsing, OutputTerminalPlusIndexed) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b[0+:4]) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0].range_kind, SpecifyRangeKind::kPlusIndexed);
}

TEST(SpecifyPathParsing, OutputTerminalMinusIndexed) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b[3-:4]) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0].range_kind, SpecifyRangeKind::kMinusIndexed);
}

}  // namespace
