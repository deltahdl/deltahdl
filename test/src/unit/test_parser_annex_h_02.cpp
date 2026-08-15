#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §H.2: "A formal argument is an open array when a range of one or more of its
// dimensions is unspecified (denoted in SystemVerilog by using empty square
// brackets, [])." The packed part is one such dimension: the annex's own list
// of formal-argument types opens with "bit[]". The pair carries no bounds, so
// nothing lands in the sized packed slots and the type is marked instead.
TEST_F(DpiParseTest, DpiImportFormalLeavesPackedRangeUnspecified) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(input bit [] a);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  ASSERT_EQ(items[0]->func_args.size(), 1u);
  const DataType& type = items[0]->func_args[0].data_type;
  EXPECT_TRUE(type.has_unsized_packed_dim);
  EXPECT_EQ(type.packed_dim_left, nullptr);
  EXPECT_TRUE(type.extra_packed_dims.empty());
  EXPECT_FALSE(diag_.HasErrors());
}

// §H.2: the two parts of a formal are unspecified independently. The annex's
// "logic [] arrayNx3 [3:1]" leaves the packed range open while giving the
// unpacked one bounds, so the open dimension must be read off the packed part
// and the sized dimension recorded on the unpacked one.
TEST_F(DpiParseTest, DpiImportFormalOpensPackedPartBesideSizedUnpackedPart) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(logic [] arrayNx3 [3:1]);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& args = unit->modules[0]->items[0]->func_args;
  ASSERT_EQ(args.size(), 1u);
  EXPECT_TRUE(args[0].data_type.has_unsized_packed_dim);
  ASSERT_EQ(args[0].unpacked_dims.size(), 1u);
  EXPECT_NE(args[0].unpacked_dims[0], nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

// §H.2: both parts may be left unspecified at once -- the annex writes this as
// "bit [] arrayNxN []". The two empty pairs stand on opposite sides of the
// declared name, and the second belongs to the unpacked part; reading it as a
// second packed dimension would lose the unpacked one entirely.
TEST_F(DpiParseTest, DpiImportFormalOpensBothPackedAndUnpackedParts) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(bit [] arrayNxN []);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& args = unit->modules[0]->items[0]->func_args;
  ASSERT_EQ(args.size(), 1u);
  EXPECT_TRUE(args[0].data_type.has_unsized_packed_dim);
  ASSERT_EQ(args[0].unpacked_dims.size(), 1u);
  EXPECT_EQ(args[0].unpacked_dims[0], nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

// §H.2: "Actual arguments' packed dimensions shall collectively match a
// solitary, unsized formal packed dimension." The unspecified dimension takes
// every packed dimension of the actual at once, so a sized dimension written
// beside it has nothing left to match and the declaration is rejected.
TEST_F(DpiParseTest, DpiImportFormalRejectsSizedPackedDimBeforeUnspecifiedOne) {
  Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(input bit [7:0] [] a);\n"
      "endmodule\n");
  // §35.5.6.1 owns the report: ValidateDpiImportOpenArrayPackedDims in
  // src/parser/parser_dpi_validate.cpp files the solitary-dimension rule
  // under the DPI open-array subclause rather than under Annex H.
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "formal argument 'a' gives a packed dimension no "
                            "range alongside a sized one",
                            2, "35.5.6.1"));
}

// §H.2: the solitary-dimension rule does not depend on which dimension is
// written first. An unspecified packed dimension followed by a sized one
// leaves the same pair of dimensions competing for the actual's packed part.
TEST_F(DpiParseTest, DpiImportFormalRejectsSizedPackedDimAfterUnspecifiedOne) {
  Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(input bit [] [7:0] a);\n"
      "endmodule\n");
  // §35.5.6.1 owns the report, as above.
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "formal argument 'a' gives a packed dimension no "
                            "range alongside a sized one",
                            2, "35.5.6.1"));
}

// §H.2: a formal is open only where a range is left *unspecified*. A packed
// dimension written with bounds is an ordinary sized one, so it must not be
// mistaken for the open form -- otherwise every vector formal would claim the
// relaxation the annex reserves for empty brackets.
TEST_F(DpiParseTest, DpiImportFormalWithSizedPackedDimIsNotOpen) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(input bit [7:0] a);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& args = unit->modules[0]->items[0]->func_args;
  ASSERT_EQ(args.size(), 1u);
  EXPECT_FALSE(args[0].data_type.has_unsized_packed_dim);
  EXPECT_NE(args[0].data_type.packed_dim_left, nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

// §H.2: "Formal arguments in SystemVerilog can be specified as open arrays
// solely in import declarations." Leaving a packed range unspecified is that
// relaxation, so the same spelling in an ordinary variable declaration -- which
// no import declaration governs -- is not admitted.
TEST_F(DpiParseTest, UnspecifiedPackedRangeIsRejectedOutsideAnImport) {
  Parse(
      "module m;\n"
      "  bit [] a;\n"
      "endmodule\n");
  // §11.2 owns the report: Parser::AtUnsizedPackedDim admits the empty pair
  // only inside a DPI import's formals, so outside one Parser::ParsePackedDims
  // reads the bracket as an ordinary packed dimension and the ']' stands where
  // the range expression is required.
  EXPECT_TRUE(
      ReportedError(diag_.Diagnostics(), "expected expression", 2, "11.2"));
}

// §H.2: the relaxation is granted to a formal argument of an import, not to
// its result. A function result carries a single value whose width the
// declaration alone fixes, with no actual to take the width from.
TEST_F(DpiParseTest, UnspecifiedPackedRangeIsRejectedOnAnImportResult) {
  Parse(
      "module m;\n"
      "  import \"DPI-C\" function bit [] f(input int a);\n"
      "endmodule\n");
  // §11.2 owns the report: Parser::ParseDpiImport parses the result type
  // before it sets in_dpi_import_formals_, so the ']' stands where the range
  // expression of an ordinary packed dimension is required.
  EXPECT_TRUE(
      ReportedError(diag_.Diagnostics(), "expected expression", 2, "11.2"));
}

}  // namespace
