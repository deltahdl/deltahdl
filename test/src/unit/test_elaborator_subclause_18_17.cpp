#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §18.17 states "The randsequence statement creates an automatic scope. All
// production identifiers are local to the scope", so the set a production
// identifier resolves against is exactly the productions its own randsequence
// statement declares. These are the two reports
// src/elaborator/elaborator_validate_randsequence.cpp makes of a name outside
// that set, one for an rs_production_item and one for the optional top-level
// name the statement's parentheses carry, each a literal fragment of the
// std::format string at its emission site.
constexpr std::string_view kItemNamesNoProduction =
    "randsequence production item names";
constexpr std::string_view kTopNameNamesNoProduction =
    "as its top-level production, which is not one of the productions it "
    "declares";

// The module, initial block and randsequence statement every case here hands
// the elaborator: `top` is the name written inside the parentheses and `rules`
// is the production list between it and endsequence. Written once so that each
// case varies only the name that fails to resolve and the position the resolver
// reaches it in, and so that seven near-identical bodies do not stand in the
// file for the copy-paste detector to find.
//
// `rules` supplies its own indentation and its own trailing newline, so the
// randsequence keyword stands on line 3 of every source built here.
std::string RandsequenceOver(std::string_view top, std::string_view rules) {
  return "module m;\n"
         "  initial begin\n"
         "    randsequence(" +
         std::string(top) + ")\n" + std::string(rules) +
         "    endsequence\n"
         "  end\n"
         "endmodule\n";
}

// Elaborates the randsequence RandsequenceOver builds and asserts the
// elaborator reported `message` on the line holding `anchor`.
//
// The anchor is passed rather than fixed because the report stands at the
// offending name now: RsProductionItem carries the location of the identifier
// it names, so a case whose name is written on the rule line is reported there
// and not at the randsequence keyword. Every case below therefore anchors on
// its own rule, and only the one about the name in the parentheses anchors on
// the keyword. Naming the line by a string it holds rather than by a number
// keeps the cases from counting the lines RandsequenceOver writes around them.
void ExpectReportedOverRandsequence(std::string_view top,
                                    std::string_view rules,
                                    std::string_view message,
                                    std::string_view anchor) {
  ElabFixture f;
  std::string src = RandsequenceOver(top, rules);
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                            LineHolding(src, anchor), "18.17"));
}

// §18.17 makes every production identifier local to the randsequence statement
// that declares it, so a production item naming a production the statement
// never declared names nothing at all. `second` is that name here and `first`
// beside it resolves, so the source differs from a legal one in the one name
// the report has to be about.
TEST(RandsequenceProductionNames, ItemNamingNoDeclaredProductionIsRejected) {
  ExpectReportedOverRandsequence("main",
                                 "      main : first second;\n"
                                 "      first : { ; };\n",
                                 kItemNamesNoProduction, "main : first second");
}

// §18.17 states that the randsequence keyword "can be followed by an optional
// production name (inside the parentheses) that designates the name of the
// top-level production", so that name has to designate one of the statement's
// productions. `mian` designates nothing over a statement declaring `main`, and
// it reaches the resolver as Stmt::rs_top_production rather than as an
// rs_production_item, which is a position a check written over production items
// alone never visits.
TEST(RandsequenceProductionNames,
     TopLevelNameDesignatingNoProductionIsRejected) {
  ExpectReportedOverRandsequence("mian", "      main : { ; };\n",
                                 kTopNameNamesNoProduction, "randsequence(");
}

// §18.17.2's rs_if_else names a production for the true branch, which the
// resolver reaches through the branch rather than through the rs_prod's own
// item. `missing` is declared nowhere; `other` beside it is declared, so the
// only thing wrong with this source is the name the report has to be about.
TEST(RandsequenceProductionNames,
     IfBranchNamingNoDeclaredProductionIsRejected) {
  ExpectReportedOverRandsequence("main",
                                 "      main : if (1) missing else other;\n"
                                 "      other : { ; };\n",
                                 kItemNamesNoProduction,
                                 "if (1) missing else other");
}

// §18.17.2's rs_if_else names a second production for the else branch, which
// the syntax and RsProd hold apart from the true branch, so a resolver reaching
// one branch does not thereby reach the other. This source is the case above
// with the two names exchanged.
TEST(RandsequenceProductionNames,
     ElseBranchNamingNoDeclaredProductionIsRejected) {
  ExpectReportedOverRandsequence("main",
                                 "      main : if (1) other else missing;\n"
                                 "      other : { ; };\n",
                                 kItemNamesNoProduction,
                                 "if (1) other else missing");
}

// §18.17.4's rs_repeat names the production it repeats, which the resolver
// reaches through the repeat rather than through the rs_prod's own item. The
// count is 2 rather than 1 or 0 so that nothing about the repetition makes the
// name reachable or unreachable by accident.
TEST(RandsequenceProductionNames, RepeatNamingNoDeclaredProductionIsRejected) {
  ExpectReportedOverRandsequence("main", "      main : repeat(2) missing;\n",
                                 kItemNamesNoProduction, "repeat(2) missing");
}

// §18.17.3's rs_case names a production in each of its arms, which the resolver
// reaches through the arm. `missing` names the arm the case expression selects
// and `other`, declared, names the default arm, so the two arms differ in
// exactly the name the report has to be about.
TEST(RandsequenceProductionNames, CaseArmNamingNoDeclaredProductionIsRejected) {
  ExpectReportedOverRandsequence(
      "main",
      "      main : case (0) 0: missing; default: other; endcase;\n"
      "      other : { ; };\n",
      kItemNamesNoProduction, "0: missing; default: other");
}

// §18.17.5's rand join names the productions it interleaves in a list of its
// own, RsRule::rand_join_items, rather than through an rs_prod, so a resolver
// walking the rs_prods alone reaches none of them. `other` beside `missing`
// resolves, so the source differs from a legal one in one name.
TEST(RandsequenceProductionNames,
     RandJoinNamingNoDeclaredProductionIsRejected) {
  ExpectReportedOverRandsequence("main",
                                 "      main : rand join missing other;\n"
                                 "      other : { ; };\n",
                                 kItemNamesNoProduction,
                                 "rand join missing other");
}

// The control the seven cases above rest on: a randsequence every one of whose
// names resolves is reported nowhere. Every position they breach one at a time
// is written here resolving -- the top-level name `main`, the two branches of
// the if, the production the repeat repeats, the productions of both case arms,
// the two the rand join interleaves, and the plain production item `leaf`.
// Without this case, a resolver reporting every name whatever it resolved to
// would satisfy all seven.
TEST(RandsequenceProductionNames, EveryNameResolvingIsReportedNowhere) {
  ElabFixture f;
  std::string src =
      RandsequenceOver("main",
                       "      main : if (1) yes else no;\n"
                       "      yes : repeat(2) pick;\n"
                       "      no : case (0) 0: pick; default: pick; endcase;\n"
                       "      pick : rand join leaf twig;\n"
                       "      twig : leaf;\n"
                       "      leaf : { ; };\n");
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(FindDiag(f, kItemNamesNoProduction), nullptr);
  EXPECT_EQ(FindDiag(f, kTopNameNamesNoProduction), nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The claim the seven cases above rest on, stated on its own: the report stands
// at the offending name and not at the statement. The randsequence keyword is
// three lines above the rule that breaks, and `first` on the rule before it
// resolves, so a report made at the statement or at the first rule reads a
// different line from this one.
TEST(RandsequenceProductionNames, ReportStandsOnTheLineOfTheOffendingItem) {
  ElabFixture f;
  std::string src = RandsequenceOver("main",
                                     "      main : first;\n"
                                     "      first : { ; };\n"
                                     "      spare : second;\n");
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kItemNamesNoProduction,
                            LineHolding(src, "spare : second"), "18.17"));
}

// Two rules naming two different undeclared productions are reported on their
// own lines. One report cannot show that the location follows the item rather
// than the statement: a location fixed at the randsequence keyword satisfies a
// case that asserts one report on one line, and satisfies it twice over when
// two reports land on that same line with nothing to tell them apart.
TEST(RandsequenceProductionNames, TwoBadNamesAreReportedOnTwoLines) {
  ElabFixture f;
  std::string src = RandsequenceOver("main",
                                     "      main : alpha;\n"
                                     "      alpha : missing_one;\n"
                                     "      spare : missing_two;\n");
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'missing_one'",
                            LineHolding(src, "alpha : missing_one"), "18.17"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'missing_two'",
                            LineHolding(src, "spare : missing_two"), "18.17"));
}

}  // namespace
