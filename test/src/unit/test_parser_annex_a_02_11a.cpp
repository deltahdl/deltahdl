#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CovergroupDeclParsing, SelectExpression_Parenthesized) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = (binsof(cp1) && binsof(cp2));\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, SelectCondition_Binsof) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, SelectCondition_BinsofIntersect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1) intersect {[0:3]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BinsExpression_CoverPointDotBin) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1.low);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverGroup_CrossWithBinsSelection) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel1 = binsof(cp1) intersect {[0:3]};\n"
              "      bins sel2 = !binsof(cp2);\n"
              "      bins sel3 = binsof(cp1) && binsof(cp2);\n"
              "      ignore_bins ig = binsof(cp1) intersect {255};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, FullCovergroup_MultipleElements) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @(posedge clk);\n"
              "    option.auto_bin_max = 64;\n"
              "    cp_addr: coverpoint addr {\n"
              "      bins low = {[0:63]};\n"
              "      bins mid = {[64:191]};\n"
              "      bins high = {[192:255]};\n"
              "    }\n"
              "    cp_data: coverpoint data;\n"
              "    cross cp_addr, cp_data;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverGroup_MultipleCoverpoints) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @(posedge clk);\n"
              "    type_option.weight = 2;\n"
              "    cp1: coverpoint a iff (enable);\n"
              "    cp2: coverpoint b;\n"
              "    cp3: coverpoint c {\n"
              "      bins low = {[0:3]};\n"
              "      bins high = {[4:7]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverGroup_PortsWithBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg(ref int x, input int threshold);\n"
              "    coverpoint x {\n"
              "      bins below = {[0:threshold]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, ErrorMissingEndgroup) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x;\n"
      "endmodule\n");
  // The unterminated body swallows 'endmodule', so the covergroup is what runs
  // out of source, and the end of the source stands on line 5, the line the
  // trailing newline opened.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endgroup', got EOF", 5, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorMissingCovergroupName) {
  auto r = Parse(
      "module m;\n"
      "  covergroup;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 2, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorMismatchedEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg1;\n"
      "  endgroup : cg2\n"
      "endmodule\n");
  // §9.3.4 owns the end-label rule Parser::MatchEndLabel enforces for every
  // named block, the covergroup included; §19.3 has no report of its own here.
  EXPECT_TRUE(ReportedError(r.diags, "end label 'cg2' does not match 'cg1'", 3,
                            "9.3.4"));
}

TEST(CovergroupDeclParsing, ErrorMissingSemicolonAfterDecl) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n");
  // 'coverpoint' stands where the ';' was demanded.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'coverpoint'", 3, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorUnclosedPortList) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg(ref int x;\n"
      "  endgroup\n"
      "endmodule\n");
  // The unclosed formal list scans to the end of the source, so the ';' that
  // ends the covergroup declaration is demanded at EOF, on line 5.
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got EOF", 5, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorCoverPointMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x\n"
      "  endgroup\n"
      "endmodule\n");
  // The unterminated coverpoint swallows 'endgroup' and 'endmodule', so the
  // covergroup runs out of source at line 6.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endgroup', got EOF", 6, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorCoverPointUnclosedBinsBlock) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a = {0};\n"
      "  endgroup\n"
      "endmodule\n");
  // The unclosed coverpoint body swallows 'endgroup', so the covergroup runs
  // out of source at line 7.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endgroup', got EOF", 7, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorCrossUnclosedBody) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins sel = binsof(cp1);\n"
      "  endgroup\n"
      "endmodule\n");
  // The unclosed cross body swallows 'endgroup', so the covergroup runs out of
  // source at line 9.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endgroup', got EOF", 9, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorCrossMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2\n"
      "  endgroup\n"
      "endmodule\n");
  // The unterminated cross swallows 'endgroup' and 'endmodule', so the
  // covergroup runs out of source at line 8.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endgroup', got EOF", 8, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorBinsMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a = {0}\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  // The coverpoint body's closing '}' on line 5 is where the missing ';' is
  // detected.
  EXPECT_TRUE(
      ReportedError(r.diags, "missing ';' in covergroup item", 5, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorBinsMissingEquals) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a {0};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  // §19.5.1 owns the bins_selection '=' the header scan demands; §19.3 has no
  // report of its own here.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '=' in bins declaration", 4, "19.5.1"));
}

TEST(CovergroupDeclParsing, ErrorBinsofMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins sel = binsof(cp1;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  // The unbalanced paren is reported where the cross body closes, on line 7.
  EXPECT_TRUE(
      ReportedError(r.diags, "missing ')' in covergroup item", 7, "19.3"));
}

TEST(CovergroupDeclParsing, MultipleCovergroupDecls) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg1;\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  covergroup cg2;\n"
      "    coverpoint y;\n"
      "  endgroup\n"
      "  covergroup cg3;\n"
      "    coverpoint z;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(CountItemsByKind(r.cu->modules[0]->items,
                             ModuleItemKind::kCovergroupDecl),
            3u);
}

TEST(CovergroupDeclParsing, CovergroupWithAllSpecTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @(posedge clk);\n"
              "    option.auto_bin_max = 64;\n"
              "    type_option.weight = 2;\n"
              "    cp1: coverpoint addr {\n"
              "      bins low = {[0:63]};\n"
              "      bins high = {[64:255]};\n"
              "      wildcard bins even = {8'b???????0};\n"
              "      illegal_bins overflow = {[256:$]};\n"
              "      ignore_bins zero = {0};\n"
              "      bins def = default;\n"
              "    }\n"
              "    cp2: coverpoint data iff (valid);\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1) intersect {[0:63]};\n"
              "      ignore_bins ig = binsof(cp1) intersect {0};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, ErrorWithFunctionWrongName) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg with function foo(int x);\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'sample', got 'foo'", 2, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorBlockEventMissingBeginOrEnd) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg @@(foo);\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'begin' or 'end' in block event",
                            2, "19.3"));
}

// A.2.11's hierarchical_btf_identifier has three forms, and the third,
// `[ hierarchical_identifier . | class_scope ] method_identifier`, names a
// method through A.8.4's class_scope, `class_type ::`. §19.3 (printed page
// 577) has the event name "a named block, task, function, or class method".
// The parser read the name as identifiers joined by '.', so the '::' was
// reported as a missing ')'.
TEST(CovergroupDeclParsing, HierarchicalBtfIdentifier_ClassScope) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin C::m);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

// class_type is `ps_class_identifier [ parameter_value_assignment ] { ::
// class_identifier [ parameter_value_assignment ] }`, so the scope may be a
// package's class specialized by a parameter value.
TEST(CovergroupDeclParsing, HierarchicalBtfIdentifier_ParameterizedClassScope) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(end pkg::C#(8)::m or begin D#(.W(4))::n);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

// A.9.3 spells hierarchical_identifier `[ $root . ] { identifier
// constant_bit_select . } identifier`, so a block inside a generate loop's
// instance is named through a select, and the path may start at $root.
TEST(CovergroupDeclParsing, HierarchicalBtfIdentifier_RootAndBitSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin $root.top.g[0].u[1][2].blk);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

// `$root` is followed by '.' in A.9.3's hierarchical_identifier; the name
// after it is not what `$root` alone names.
TEST(CovergroupDeclParsing,
     HierarchicalBtfIdentifier_RootWithoutDotIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg @@(begin $root top.t);\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected '.'", 2, "A.2.11"));
}

// coverage_option is `option . member_identifier = expression`, and nothing
// shorter: a member named with no value sets nothing. The parser read the
// keyword and the member and skipped to the ';', so the form was accepted.
TEST(CovergroupDeclParsing, CoverageOption_MemberWithoutValueIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    option.auto_bin_max;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a coverage option is set as 'option.member = value'", 3,
      "A.2.11"));
}

// The other half of the form: `type_option . member_identifier =
// constant_expression` names a member before its value.
TEST(CovergroupDeclParsing, CoverageOption_KeywordWithoutMemberIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    type_option = 3;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a coverage option is set as 'type_option.member = value'", 3,
      "A.2.11"));
}

// bins_or_options lists coverage_option among a cover_point's body items, and
// the form is the same there.
TEST(CovergroupDeclParsing, CoverageOption_InCoverpointBodyWithoutValue) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      option.weight;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a coverage option is set as 'option.member = value'", 4,
      "A.2.11"));
}

// bins_selection_or_option lists coverage_option among a cross_body's items;
// a type_option there was not read at all before.
TEST(CovergroupDeclParsing, CoverageOption_InCrossBodyWithoutMember) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    a: coverpoint x;\n"
      "    b: coverpoint y;\n"
      "    cross a, b {\n"
      "      type_option = 1;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a coverage option is set as 'type_option.member = value'", 6,
      "A.2.11"));
}

// coverage_spec_or_option opens both alternatives with `{ attribute_instance
// }`. The parser knew no item that opened with one and skipped to the first
// ';', which for a coverpoint with a body lies inside the braces, so the body
// went unread: the bins written with no '=' here drew no report.
TEST(CovergroupDeclParsing, AttributeInstance_PrecedesCoverageSpec) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    (* full *) coverpoint x {\n"
      "      bins b {1};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '=' in bins declaration", 4, "19.5.1"));
}

// The same for the coverage_option alternative: an option behind an attribute
// was skipped rather than recorded, so §19.7's rule against assigning an
// option twice in one covergroup did not see the first assignment.
TEST(CovergroupDeclParsing, AttributeInstance_PrecedesCoverageOption) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    (* a = 1 *) option.weight = 1;\n"
      "    option.weight = 2;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "coverage option 'option.weight' is assigned more than once", 4,
      "19.7"));
}

// A cover_point whose label carries a data_type_or_implicit opened with a
// token the parser took for no item, and was skipped to the first ';' with
// its body unread.
TEST(CovergroupDeclParsing, CoverPoint_DataTypeBeforeLabelReadsBody) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    int cp: coverpoint x {\n"
      "      bins b {1};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '=' in bins declaration", 4, "19.5.1"));
}

// A.2.2.1's implicit_data_type is `[ signing ] { packed_dimension }`, so a
// signing or a packed dimension alone types the coverpoint.
TEST(CovergroupDeclParsing, CoverPoint_ImplicitDataTypeBeforeLabel) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    signed [7:0] cp1: coverpoint x;\n"
              "    [3:0] cp2: coverpoint y;\n"
              "  endgroup\n"
              "endmodule\n"));
}

// cover_point is `coverpoint expression [ iff ( expression ) ] bins_or_empty`;
// the expression is not optional.
TEST(CovergroupDeclParsing, CoverPoint_WithoutExpressionIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp: coverpoint;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a coverpoint covers an expression; none is written", 3,
      "A.2.11"));
}

// The expression is read as one: the parser skipped to the first '{' and so
// took a concatenation for the body, leaving the body itself unread.
TEST(CovergroupDeclParsing, CoverPoint_ConcatenationExpressionThenBody) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint {a, b} {\n"
      "      bins b {1};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '=' in bins declaration", 4, "19.5.1"));
}

// The guard is `iff ( expression )`, its expression parenthesized.
TEST(CovergroupDeclParsing, CoverPoint_BareIffGuardIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x iff en;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a coverage guard is written 'iff ( expression )'",
                            3, "A.2.11"));
}

// cover_cross carries the same `[ iff ( expression ) ]` after its
// list_of_cross_items.
TEST(CovergroupDeclParsing, CoverCross_BareIffGuardIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    a: coverpoint x;\n"
      "    b: coverpoint y;\n"
      "    cross a, b iff en {\n"
      "      bins s = binsof(a);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a coverage guard is written 'iff ( expression )'",
                            5, "A.2.11"));
}

// cross_body holds bins_selection, `bins_keyword bin_identifier =
// select_expression [ iff ( expression ) ]`, which admits no `wildcard`; the
// four forms that do are bins_or_options, a cover_point's.
TEST(CovergroupDeclParsing, BinsSelection_WildcardInCrossIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    a: coverpoint x;\n"
      "    b: coverpoint y;\n"
      "    cross a, b {\n"
      "      wildcard bins s = binsof(a);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "a bins_selection admits no 'wildcard'", 6,
                            "A.2.11"));
}

// Nor does bins_selection subscript its name.
TEST(CovergroupDeclParsing, BinsSelection_ArrayInCrossIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    a: coverpoint x;\n"
      "    b: coverpoint y;\n"
      "    cross a, b {\n"
      "      bins s[] = binsof(a);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "a cross bin is not an array", 6, "A.2.11"));
}

// select_expression has no `default` form.
TEST(CovergroupDeclParsing, BinsSelection_DefaultInCrossIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    a: coverpoint x;\n"
      "    b: coverpoint y;\n"
      "    cross a, b {\n"
      "      bins s = default;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "'default' is a coverpoint bin", 6, "A.2.11"));
}

// bins_or_options writes `[ wildcard ]` on its value and transition forms and
// on neither `default` form.
TEST(CovergroupDeclParsing, BinsOrOptions_WildcardDefaultIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      wildcard bins d = default;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "a 'default' bin takes none", 4, "A.2.11"));
}

// `bins_keyword bin_identifier = default sequence` subscripts nothing, where
// the `default` form before it carries `[ [ [ covergroup_expression ] ] ]`.
TEST(CovergroupDeclParsing, BinsOrOptions_DefaultSequenceArrayIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins d[] = default sequence;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "a 'default sequence' bin is not an array",
                            4, "A.2.11"));
}

// A transition bin's array is `[ ]` alone: §19.5.2 (printed page 592) names
// its bins "binname[transition]" for the transitions the list holds, so the
// declaration gives no size.
TEST(CovergroupDeclParsing, BinsOrOptions_SizedTransitionArrayIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins t[4] = (1 => 2), (2 => 3);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a transition bin's array is written '[ ]'", 4, "A.2.11"));
}

// What the four rejections above leave standing: `wildcard` on a transition
// bin with its `[ ]`, a sized array on a value bin, and a `default` bin with
// its own array.
TEST(CovergroupDeclParsing, BinsOrOptions_WildcardTransitionAndSizedValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      wildcard bins t[] = (4'b1x0x => 4'b0xx1);\n"
              "      bins v[4] = {[0:15]};\n"
              "      bins d[2] = default;\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace
