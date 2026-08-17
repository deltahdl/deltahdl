#include <cstddef>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_included_keyword_elab.h"
#include "helpers_keyword_sweep_skips.h"
#include "helpers_keyword_version.h"
#include "helpers_reported_error.h"
#include "helpers_reserved_keyword_elab.h"
#include "helpers_rtlir_lookup.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {
// The first included list, swept at this stage. There is no earlier version to
// pair these against -- they have been reserved since the first of the three
// lists this version names -- so the accepting side of the claim is the test
// below, where the same words build the design in their keyword roles.
TEST(SystemVerilog2005KeywordElaboration, IncludedVerilog1995WordsAreReserved) {
  ExpectKeywordTableIsReserved("1800-2005", kSweepTable221);
}

// The second included list at this stage, swept whole. Each of Table 22-2's
// entries is reserved here, and under "1364-1995" -- the first of the three
// lists this version includes, where it is not yet a keyword -- the same
// declaration elaborates into a variable of the width it asked for. The pair is
// what makes each word an inclusion rather than an unrelated failure.
TEST(SystemVerilog2005KeywordElaboration, IncludedVerilog2001WordsAreReserved) {
  ExpectKeywordTableIsReserved("1800-2005", kSweepTable222);
}

// The third included list. Its one word cannot name an elaborated variable
// here, names one under both of the lists the version it comes from is built
// on, and still carries its net type into the design -- inclusion means the
// keyword role survives, not only that the identifier slot closes.
TEST(SystemVerilog2005KeywordElaboration, IncludedVerilog2005WordIsReserved) {
  ExpectKeywordTableIsReserved("1800-2005", kSweepTable223);
  ExpectTable223DeclarationsElaborate("1800-2005");
}

// Table 22-4 swept whole at this stage, with the leg that makes each entry an
// addition. The word cannot name an elaborated variable here, and under
// "1364-2005" -- the union of everything this version includes -- the same
// declaration reaches the design as a variable of the width it asked for.
// Reading the variable back is what keeps the accepting leg from being any
// elaboration that happens to succeed.
TEST(SystemVerilog2005KeywordElaboration, AddedWordsCannotNameVariables) {
  ExpectKeywordTableIsReserved("1800-2005", kSweepTable224);
}

// Table 22-4 doing the elaborated jobs its words exist for, which is the half a
// reserved-word sweep cannot show. The data types are read back with their
// widths and with the four-state flag that separates the two-state additions
// from `reg` and `logic`; `typedef` and `enum` name types whose members the
// elaborator resolves; the process words each reach the design as a process of
// their own kind; and the design element words open elements the elaborator
// distinguishes. The same source is not a design at all under the union of
// everything this version includes, which is what makes every one of them an
// addition of this version rather than something inherited.
TEST(SystemVerilog2005KeywordElaboration, AddedWordsDoTheirElaboratedJobs) {
  ExpectTable224DeclarationsElaborate("1800-2005");
}

// The declaration forms the test above does not reach, carried into the
// elaborated design. A declaration may bring its own initializer along, a port
// may be typed in the module header, and a port may instead be typed in the
// body in the separate style where the header lists only names. Each is a
// production of its own, and the added type words are observed across a
// hierarchy here rather than inside one module -- the child's ports carry the
// added types and the parent binds objects of those types to them.
TEST(SystemVerilog2005KeywordElaboration,
     AddedTypeWordsTypeEveryDeclarationForm) {
  ExpectEveryDeclarationFormElaborates("1800-2005");
}

// A parameter declaration is a syntactic position of its own for the added type
// words, and one that feeds the constant-expression axis rather than the
// storage axis: the type qualifies a constant, and that constant then has to
// resolve and be usable where a constant expression is required. Both the
// overridable and the local form are here because they reach the elaborator by
// different paths, and the typed parameter is then spent on a declaration's
// width so the value is observed being consumed rather than merely stored.
TEST(SystemVerilog2005KeywordElaboration, AddedTypeWordsQualifyConstants) {
  const std::string kSrc =
      "module t;\n"
      "  parameter  int  P = 21;\n"
      "  localparam byte S = 8'd1;\n"
      "  logic [P-1:0] from_typed_parameter;\n"
      "  logic [S+6:0]  from_typed_localparam;\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(InSv2005(kSrc), f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* p = FindParam(design, "t", "P");
  ASSERT_NE(p, nullptr);
  EXPECT_FALSE(p->is_localparam);
  EXPECT_EQ(p->resolved_value, 21);

  const auto* s = FindParam(design, "t", "S");
  ASSERT_NE(s, nullptr);
  EXPECT_TRUE(s->is_localparam);
  EXPECT_EQ(s->resolved_value, 1);

  const auto* wide = FindVar(design, "t", "from_typed_parameter");
  ASSERT_NE(wide, nullptr);
  EXPECT_EQ(wide->width, 21u);
  const auto* narrow = FindVar(design, "t", "from_typed_localparam");
  ASSERT_NE(narrow, nullptr);
  EXPECT_EQ(narrow->width, 8u);

  ElabFixture included;
  // Under "1364-2005" the type words this source is built from are ordinary
  // identifiers, so the parameter declaration loses its type and its name at
  // once and Parser::ParseParamDecl in src/parser/parser_types.cpp reports. The
  // rejection is the parser's, so the source is not required to parse.
  ElaborateWithPreprocessorAllowingParseErrors(In2005(kSrc), included, "t");
  EXPECT_TRUE(ReportedError(included.diag.Diagnostics(),
                            "parameter declaration requires a default value",
                            LineInRegion(2), "6.20.1"));
}

// Table 22-1 doing its work under this version, read back as elaborated
// structure. The net types are the sharpest part: each resolved and driven type
// the first included list names has to survive into the design as itself rather
// than collapsing onto a plain wire, which would leave the inclusion
// unobserved.
TEST(SystemVerilog2005KeywordElaboration,
     IncludedVerilog1995WordsStillBuildDesign) {
  ExpectTable221DeclarationsElaborate("1800-2005");
}

// Table 22-2 doing its work, likewise as structure rather than as tokens.
// `localparam` resolves to a constant, `genvar`/`generate`/`endgenerate`
// produce one copy of the loop body per iteration, and `signed`/`unsigned`
// select what they select. The three are tied together on purpose: the
// localparam is the loop bound, so the count of declarations reaching the
// design depends on it resolving, and the nested condition picks out a single
// iteration, so the genvar has to hold a different constant on each pass.
TEST(SystemVerilog2005KeywordElaboration,
     IncludedVerilog2001WordsStillBuildDesign) {
  ExpectTable222DeclarationsElaborate("1800-2005");
}

// The constant forms that reach a declaration's width, which is where a
// constant expression is actually required. A literal and a `parameter` come
// from the first included list, `localparam` and the `automatic` that lets a
// constant function be written come from the second, and `int` -- the type the
// function returns and the declarations take -- is one of this version's own
// additions. So the four forms are reachable here by what this version includes
// and are written with what it adds, and the width the design ends up with is
// what shows each constant resolved.
//
// The remaining constant form, a genvar, shows its value in the copies its loop
// produces rather than in a width, and it is observed doing exactly that in
// IncludedVerilog2001WordsStillBuildDesign above -- there against a loop bound
// that is itself a constant and with a nested condition singling out one
// iteration. Repeating a weaker version of it here would add nothing.
TEST(SystemVerilog2005KeywordElaboration,
     EveryConstantFormResolvesUnderThisVersion) {
  ExpectEveryConstantFormResolves("1800-2005", "", "");
}

// The negative the four tables imply, carried to this stage. A word none of
// them lists is an ordinary identifier here, so it names an object that really
// reaches the design -- and it is not a data type, which is the half that would
// go unchecked if only the naming side were tested.
TEST(SystemVerilog2005KeywordElaboration,
     UnlistedWordsNameObjectsButAreNotTypes) {
  ExpectWordsNameObjectsButAreNotTypes(
      "1800-2005", {"until", "let", "global", "nettype", "soft"});
}

}  // namespace
