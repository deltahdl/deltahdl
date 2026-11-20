#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST_F(DpiParseTest, DpiImportOpenArrayFormalAccepted) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f2(logic [127:0] i []);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  ASSERT_EQ(items[0]->func_args.size(), 1u);
  ASSERT_EQ(items[0]->func_args[0].unpacked_dims.size(), 1u);
  EXPECT_EQ(items[0]->func_args[0].unpacked_dims[0], nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(DpiParseTest, DpiImportMultiDimensionOpenArrayFormalAccepted) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f3(input int i [][]);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  ASSERT_EQ(items[0]->func_args.size(), 1u);
  ASSERT_EQ(items[0]->func_args[0].unpacked_dims.size(), 2u);
  EXPECT_EQ(items[0]->func_args[0].unpacked_dims[0], nullptr);
  EXPECT_EQ(items[0]->func_args[0].unpacked_dims[1], nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(DpiParseTest, DpiImportSizedUnpackedFormalIsNotOpen) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void g(input int packet [1:10]);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  ASSERT_EQ(items[0]->func_args.size(), 1u);
  ASSERT_EQ(items[0]->func_args[0].unpacked_dims.size(), 1u);
  EXPECT_NE(items[0]->func_args[0].unpacked_dims[0], nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

std::string ImportWithFormal(const char* formal) {
  return std::string("module m;\n  import \"DPI-C\" function void f(") +
         formal + ");\nendmodule\n";
}

void ExpectUnsizedPackedBesideSizedRefused(const char* formal) {
  auto r = Parse(ImportWithFormal(formal));
  EXPECT_TRUE(ReportedError(
      r.diags,
      "formal argument 'a' gives a packed dimension no range alongside a "
      "sized one; a packed dimension left unspecified must be the only packed "
      "dimension of the argument",
      2, "35.5.6.1"));
}

void ExpectFormalAccepted(const char* formal) {
  auto r = Parse(ImportWithFormal(formal));
  EXPECT_FALSE(r.has_errors);
}

TEST(DpiOpenPackedDimension, AnUnsizedDimensionBeforeASizedOneIsRefused) {
  ExpectUnsizedPackedBesideSizedRefused("input bit [] [3:0] a");
}

TEST(DpiOpenPackedDimension, AnUnsizedDimensionAfterASizedOneIsRefused) {
  ExpectUnsizedPackedBesideSizedRefused("input logic [3:0] [] a");
}

TEST(DpiOpenPackedDimension, ASoleUnsizedDimensionWithOpenUnpackedIsAccepted) {
  ExpectFormalAccepted("input bit [] a []");
}

TEST(DpiOpenPackedDimension, ASoleUnsizedDimensionWithSizedUnpackedIsAccepted) {
  ExpectFormalAccepted("input logic [] a [3:1]");
}

TEST(DpiOpenPackedDimension, ASoleUnsizedDimensionWithNoNameIsAccepted) {
  ExpectFormalAccepted("input bit []");
}

TEST(DpiOpenPackedDimension, SeveralSizedDimensionsBesideOpenUnpackedAreOk) {
  ExpectFormalAccepted("input bit [3:0] [1:0] a [][]");
}

}  // namespace
