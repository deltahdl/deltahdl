#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_notation.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::vector<std::string> Labels(GrammarProduction production) {
  std::vector<std::string> labels;
  for (const auto& form : ProductionForms(production)) {
    labels.push_back(form.label);
  }
  return labels;
}

TEST(AbstractGrammar, UnclockedSequenceProductionForms) {
  EXPECT_EQ(
      Labels(GrammarProduction::kUnclockedSequence),
      (std::vector<std::string>{
          "boolean", "local variable declaration", "local variable sampling",
          "parenthesis", "concatenation", "fusion", "or", "intersect",
          "first match", "null repetition", "unbounded repetition"}));
}

TEST(AbstractGrammar, ClockedSequenceProductionForms) {
  EXPECT_EQ(Labels(GrammarProduction::kClockedSequence),
            (std::vector<std::string>{"clock", "local variable declaration",
                                      "parenthesized", "concatenation"}));
}

TEST(AbstractGrammar, ClockedSequenceClockFormOperands) {
  const auto kForms = ProductionForms(GrammarProduction::kClockedSequence);
  ASSERT_FALSE(kForms.empty());
  EXPECT_EQ(kForms.front().operands, (std::vector<std::string>{"b", "R"}));
}

TEST(AbstractGrammar, UnclockedPropertyProductionForms) {
  EXPECT_EQ(Labels(GrammarProduction::kUnclockedProperty),
            (std::vector<std::string>{
                "strong sequence", "weak sequence",
                "local variable declaration", "parenthesis", "negation", "or",
                "and", "implication", "nexttime", "until", "abort"}));
}

TEST(AbstractGrammar, UnclockedPropertyImplicationOperands) {
  const auto kForms = ProductionForms(GrammarProduction::kUnclockedProperty);
  bool found = false;
  for (const auto& form : kForms) {
    if (form.label == "implication") {
      found = true;
      EXPECT_EQ(form.operands, (std::vector<std::string>{"R", "P"}));
    }
  }
  EXPECT_TRUE(found);
}

TEST(AbstractGrammar, ClockedPropertyProductionForms) {
  EXPECT_EQ(Labels(GrammarProduction::kClockedProperty),
            (std::vector<std::string>{
                "clock", "strong sequence", "weak sequence",
                "local variable declaration", "parenthesis", "negation", "or",
                "and", "implication", "nexttime", "until", "abort"}));
}

TEST(AbstractGrammar, ClockedPropertyImplicationOperands) {
  const auto kForms = ProductionForms(GrammarProduction::kClockedProperty);
  bool found = false;
  for (const auto& form : kForms) {
    if (form.label == "implication") {
      found = true;
      EXPECT_EQ(form.operands, (std::vector<std::string>{"S", "Q"}));
    }
  }
  EXPECT_TRUE(found);
}

TEST(AbstractGrammar, UnclockedTopLevelPropertyProductionForms) {
  EXPECT_EQ(
      Labels(GrammarProduction::kUnclockedTopLevelProperty),
      (std::vector<std::string>{"plain", "disable",
                                "local variable declaration", "parenthesis"}));
}

TEST(AbstractGrammar, ClockedTopLevelPropertyProductionForms) {
  EXPECT_EQ(
      Labels(GrammarProduction::kClockedTopLevelProperty),
      (std::vector<std::string>{"plain", "disable",
                                "local variable declaration", "parenthesis"}));
}

TEST(AbstractGrammar, AssertionProductionForms) {
  EXPECT_EQ(Labels(GrammarProduction::kAssertion),
            (std::vector<std::string>{"always", "always with clock", "initial",
                                      "initial with clock"}));
}

TEST(AbstractGrammar, AssertionFormOperandsDistinguishClockedBodies) {
  const auto kForms = ProductionForms(GrammarProduction::kAssertion);
  ASSERT_EQ(kForms.size(), 4u);
  EXPECT_EQ(kForms[0].operands, (std::vector<std::string>{"U"}));
  EXPECT_EQ(kForms[1].operands, (std::vector<std::string>{"b", "T"}));
  EXPECT_EQ(kForms[2].operands, (std::vector<std::string>{"U"}));
  EXPECT_EQ(kForms[3].operands, (std::vector<std::string>{"b", "T"}));
}

TEST(AbstractGrammar, ProductionCategoriesMatchNotation) {
  const auto kRCategory = ClassifyAnnexFNotation("R");
  ASSERT_TRUE(kRCategory.has_value());
  if (!kRCategory.has_value()) return;
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kUnclockedSequence),
            *kRCategory);
  const auto kSCategory = ClassifyAnnexFNotation("S");
  ASSERT_TRUE(kSCategory.has_value());
  if (!kSCategory.has_value()) return;
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kClockedSequence),
            *kSCategory);
  const auto kPCategory = ClassifyAnnexFNotation("P");
  ASSERT_TRUE(kPCategory.has_value());
  if (!kPCategory.has_value()) return;
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kUnclockedProperty),
            *kPCategory);
  const auto kQCategory = ClassifyAnnexFNotation("Q");
  ASSERT_TRUE(kQCategory.has_value());
  if (!kQCategory.has_value()) return;
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kClockedProperty),
            *kQCategory);
  const auto kTCategory = ClassifyAnnexFNotation("T");
  ASSERT_TRUE(kTCategory.has_value());
  if (!kTCategory.has_value()) return;
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kUnclockedTopLevelProperty),
            *kTCategory);
  const auto kUCategory = ClassifyAnnexFNotation("U");
  ASSERT_TRUE(kUCategory.has_value());
  if (!kUCategory.has_value()) return;
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kClockedTopLevelProperty),
            *kUCategory);
  const auto kACategory = ClassifyAnnexFNotation("A");
  ASSERT_TRUE(kACategory.has_value());
  if (!kACategory.has_value()) return;
  EXPECT_EQ(CategoryOfProduction(GrammarProduction::kAssertion), *kACategory);
}

TEST(AbstractGrammar, SequenceModelRepresentsUnclockedForms) {
  auto b = SeqBoolean(BoolAtom("a"));
  EXPECT_EQ(b->kind, SequenceExpr::Kind::kBoolean);
  EXPECT_EQ(SeqParen(b)->kind, SequenceExpr::Kind::kParen);
  EXPECT_EQ(SeqConcat(b, b)->kind, SequenceExpr::Kind::kConcat);
  EXPECT_EQ(SeqFusion(b, b)->kind, SequenceExpr::Kind::kFusion);
  EXPECT_EQ(SeqOr(b, b)->kind, SequenceExpr::Kind::kOr);
  EXPECT_EQ(SeqIntersect(b, b)->kind, SequenceExpr::Kind::kIntersect);
  EXPECT_EQ(SeqFirstMatch(b)->kind, SequenceExpr::Kind::kFirstMatch);
  EXPECT_EQ(SeqNullRepeat(b)->kind, SequenceExpr::Kind::kNullRepeat);
  EXPECT_EQ(SeqUnboundedRepeat(b)->kind, SequenceExpr::Kind::kUnboundedRepeat);
  EXPECT_EQ(SeqLocalVarSampling("v")->kind,
            SequenceExpr::Kind::kLocalVarSampling);
  EXPECT_EQ(SeqLocalVarDecl("int", "v", b)->kind,
            SequenceExpr::Kind::kLocalVarDecl);
}

TEST(AbstractGrammar, ClockFormDistinguishesClockedSequences) {
  auto unclocked =
      SeqConcat(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  EXPECT_FALSE(ContainsClock(*unclocked));

  auto clocked = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(ContainsClock(*clocked));

  auto nested = SeqConcat(SeqBoolean(BoolAtom("a")), clocked);
  EXPECT_TRUE(ContainsClock(*nested));
}

TEST(AbstractGrammar, NondegenerateSequenceOperandIsAccepted) {
  auto b = SeqBoolean(BoolAtom("a"));
  EXPECT_TRUE(SequenceOperandSatisfiesNondegeneracyRequirement(*b));
}

TEST(AbstractGrammar, EmptyOnlySequenceOperandIsRejected) {
  auto empty_only = SeqNullRepeat(SeqBoolean(BoolAtom("a")));
  EXPECT_FALSE(SequenceOperandSatisfiesNondegeneracyRequirement(*empty_only));
}

TEST(AbstractGrammar, SequenceOperandMatchingEmptyWordIsRejected) {
  auto b = SeqBoolean(BoolAtom("a"));
  auto admits_empty_too = SeqOr(SeqNullRepeat(b), b);
  EXPECT_FALSE(
      SequenceOperandSatisfiesNondegeneracyRequirement(*admits_empty_too));
}

TEST(AbstractGrammar, NondegenerateClockedSequenceOperandIsAccepted) {
  auto clocked = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(SequenceOperandSatisfiesNondegeneracyRequirement(*clocked));
}

TEST(AbstractGrammar, DegenerateClockedSequenceOperandIsRejected) {
  auto clocked =
      SeqClock(BoolAtom("clk"), SeqNullRepeat(SeqBoolean(BoolAtom("a"))));
  EXPECT_FALSE(SequenceOperandSatisfiesNondegeneracyRequirement(*clocked));
}

TEST(AbstractGrammar, NondegenerateLocalVariableSamplingOperandIsAccepted) {
  auto sampling = SeqLocalVarSampling("v");
  EXPECT_TRUE(SequenceOperandSatisfiesNondegeneracyRequirement(*sampling));
}

TEST(AbstractGrammar, DegenerateLocalVariableOperandIsRejected) {
  auto empty_only =
      SeqLocalVarDecl("int", "v", SeqNullRepeat(SeqBoolean(BoolAtom("a"))));
  EXPECT_FALSE(SequenceOperandSatisfiesNondegeneracyRequirement(*empty_only));
}

TEST(AbstractGrammar, LocalVariableOperandMatchingEmptyWordIsRejected) {
  auto admits_empty_too =
      SeqOr(SeqNullRepeat(SeqBoolean(BoolAtom("a"))), SeqLocalVarSampling("v"));
  EXPECT_FALSE(
      SequenceOperandSatisfiesNondegeneracyRequirement(*admits_empty_too));
}

constexpr const char* kSignals = "  logic clk0, clk1, sig0, sig1;\n";

constexpr const char* kClockedSequences =
    "  sequence sc0; @(posedge clk0) sig0 ##1 sig1; endsequence "
    "sequence sc1; @(posedge clk1) sig0 ##1 sig1; endsequence\n";

constexpr const char* kRepeatedOnAnotherClock =
    "a repeated sequence may name no clocking event other than the one in "
    "force where it is written";

struct RepetitionPlace {
  std::string name;
  std::string source;
  std::vector<int> lines;
};

std::string DeclaredOnClk0(const std::string& body) {
  return "  sequence r; @(posedge clk0) " + body +
         "; endsequence\n"
         "  property q; @(posedge clk0) " +
         body + "; endproperty\n";
}

std::string AssertedOnClk0(const std::string& body) {
  return "  assert property (@(posedge clk0) " + body + ");\n";
}

std::string InstancedBy(const std::string& unit, const std::string& end,
                        const std::string& items, const std::string& instance) {
  return unit + kSignals + kClockedSequences + items + end + "module m;\n" +
         instance + "endmodule\n";
}

std::vector<RepetitionPlace> ModulePlace(const std::string& body) {
  return {{"module",
           std::string("module m;\n") + kSignals + kClockedSequences +
               DeclaredOnClk0(body) + AssertedOnClk0(body) + "endmodule\n",
           {4, 5, 6}}};
}

std::vector<RepetitionPlace> InstancedPlaces(const std::string& body) {
  const std::string kAll = DeclaredOnClk0(body) + AssertedOnClk0(body);
  return {
      {"interface",
       InstancedBy("interface i;\n", "endinterface\n", kAll, "  i u();\n"),
       {4, 5, 6}},
      {"program",
       InstancedBy("program pr;\n", "endprogram\n", kAll, "  pr u();\n"),
       {4, 5, 6}},
      {"checker",
       "checker c(input logic clk0, input logic clk1, input logic sig0, "
       "input logic sig1);\n" +
           std::string(kClockedSequences) + kAll + "endchecker\nmodule m;\n" +
           kSignals + "  c u(clk0, clk1, sig0, sig1);\nendmodule\n",
       {3, 4, 5}},
      {"generate block",
       std::string("module m;\n") + kSignals + kClockedSequences +
           "  if (1) begin : g\n" + kAll + "  end\nendmodule\n",
       {5, 6, 7}},
  };
}

std::vector<RepetitionPlace> DeclarationOnlyPlaces(const std::string& body) {
  const std::string kUse = "  assert property (q);\n";
  return {
      {"package",
       InstancedBy("package p;\n", "endpackage\n", DeclaredOnClk0(body),
                   "  import p::*;\n" + kUse),
       {4, 5}},
      {"compilation unit",
       std::string(kSignals) + kClockedSequences + DeclaredOnClk0(body) +
           "module m;\n" + kUse + "endmodule\n",
       {3, 4}},
  };
}

std::vector<RepetitionPlace> EveryPlace(const std::string& body) {
  std::vector<RepetitionPlace> places = ModulePlace(body);
  for (const auto& more :
       {InstancedPlaces(body), DeclarationOnlyPlaces(body)}) {
    places.insert(places.end(), more.begin(), more.end());
  }
  return places;
}

void ExpectReportedInEach(
    const std::vector<std::string>& bodies,
    std::vector<RepetitionPlace> (*places)(const std::string&)) {
  for (const auto& body : bodies) {
    for (const auto& place : places(body)) {
      ElabFixture f;
      Elaborate(place.source, f);
      for (int line : place.lines) {
        EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kRepeatedOnAnotherClock,
                                  line, "F.3.2"))
            << body << " in a " << place.name << " at line " << line;
      }
    }
  }
}

void ExpectAcceptedInEach(
    const std::vector<std::string>& bodies,
    std::vector<RepetitionPlace> (*places)(const std::string&)) {
  for (const auto& body : bodies) {
    for (const auto& place : places(body)) {
      ElabFixture f;
      auto* design = ElaborateSrc(place.source, f);
      EXPECT_NE(design, nullptr) << body << " in a " << place.name;
      EXPECT_FALSE(f.has_errors) << body << " in a " << place.name;
    }
  }
}

std::vector<std::string> UnboundedOnClk1() {
  return {"(@(posedge clk1) sig0 ##1 sig1)[*1:$]",
          "(@(posedge clk1) sig0 ##1 sig1)[+]",
          "(@(posedge clk1) sig0 ##1 sig1)[*] ##1 sig0"};
}

std::vector<std::string> UnboundedOnClk0() {
  return {"(@(posedge clk0) sig0 ##1 sig1)[*1:$]",
          "(@(posedge clk0) sig0 ##1 sig1)[+]",
          "(@(posedge clk0) sig0 ##1 sig1)[*] ##1 sig0"};
}

std::vector<std::string> InstanceInAGroupOnClk1() {
  return {"(sc1 ##1 sig0)[*2]"};
}
std::vector<std::string> InstanceInAGroupOnClk0() {
  return {"(sc0 ##1 sig0)[*2]"};
}

std::vector<std::string> NestedGroupOnClk1() {
  return {"((@(posedge clk1) sig0) ##1 sig1)[*2]"};
}
std::vector<std::string> NestedGroupOnClk0() {
  return {"((@(posedge clk0) sig0) ##1 sig1)[*2]"};
}

std::vector<std::string> InstanceRangeOnClk1() {
  return {"sc1[*1:2]", "sc1[+]"};
}
std::vector<std::string> InstanceRangeOnClk0() {
  return {"sc0[*1:2]", "sc0[+]"};
}

std::vector<std::string> EveryFormOnClk1() {
  std::vector<std::string> forms = {"(@(posedge clk1) sig0 ##1 sig1)[*2]",
                                    "(@(posedge clk1) sig0 ##1 sig1)[*1:2]",
                                    "(@(posedge clk1) sig0)[*2]",
                                    "(@(posedge clk1) sig0 and sig1)[*2]",
                                    "(sig0 ##1 @(posedge clk1) sig1)[*2]",
                                    "sc1[*2]"};
  for (const auto& group :
       {UnboundedOnClk1, NestedGroupOnClk1, InstanceRangeOnClk1}) {
    auto more = group();
    forms.insert(forms.end(), more.begin(), more.end());
  }
  return forms;
}

std::vector<std::string> EveryFormOnClk0() {
  std::vector<std::string> forms = {
      "(@(posedge clk0) sig0 ##1 sig1)[*2]",
      "(@(posedge clk0) sig0 ##1 sig1)[*1:2]", "(@(posedge clk0) sig0)[*2]",
      "(@(posedge clk0) sig0 and sig1)[*2]", "sc0[*2]"};
  for (const auto& group : {UnboundedOnClk0, InstanceInAGroupOnClk0,
                            NestedGroupOnClk0, InstanceRangeOnClk0}) {
    auto more = group();
    forms.insert(forms.end(), more.begin(), more.end());
  }
  return forms;
}

TEST(RepetitionOfAClockedSequence,
     AnUnboundedRepetitionOnAnotherClockIsReported) {
  ExpectReportedInEach(UnboundedOnClk1(), ModulePlace);
}

TEST(RepetitionOfAClockedSequence,
     AnUnboundedRepetitionOnTheClockInForceIsLegal) {
  ExpectAcceptedInEach(UnboundedOnClk0(), ModulePlace);
}

TEST(RepetitionOfAClockedSequence,
     DISABLED_AGroupHoldingAnInstanceOnAnotherClockIsReported) {
  ExpectReportedInEach(InstanceInAGroupOnClk1(), EveryPlace);
}

TEST(RepetitionOfAClockedSequence,
     AGroupHoldingAnInstanceOnTheClockInForceIsLegal) {
  ExpectAcceptedInEach(InstanceInAGroupOnClk0(), EveryPlace);
}

TEST(RepetitionOfAClockedSequence, ANestedGroupOnAnotherClockIsReported) {
  ExpectReportedInEach(NestedGroupOnClk1(), ModulePlace);
}

TEST(RepetitionOfAClockedSequence, ANestedGroupOnTheClockInForceIsLegal) {
  ExpectAcceptedInEach(NestedGroupOnClk0(), ModulePlace);
}

TEST(RepetitionOfAClockedSequence,
     AnInstanceRepeatedByARangeOnAnotherClockIsReported) {
  ExpectReportedInEach(InstanceRangeOnClk1(), ModulePlace);
}

TEST(RepetitionOfAClockedSequence,
     AnInstanceRepeatedByARangeOnTheClockInForceIsLegal) {
  ExpectAcceptedInEach(InstanceRangeOnClk0(), ModulePlace);
}

std::string PackageSequenceRepeated(const std::string& name) {
  return "package p;\n" + std::string(kSignals) +
         "  sequence s0; @(posedge clk0) sig0 ##1 sig1; endsequence "
         "sequence s1; @(posedge clk1) sig0 ##1 sig1; endsequence\n"
         "endpackage\n"
         "module m;\n"
         "  assert property (@(posedge p::clk0) p::" +
         name + "[*2]);\nendmodule\n";
}

TEST(RepetitionOfAClockedSequence,
     DISABLED_APackageSequenceOnAnotherClockRepeatedIsReported) {
  ElabFixture f;
  Elaborate(PackageSequenceRepeated("s1"), f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kRepeatedOnAnotherClock, 6, "F.3.2"));
}

TEST(RepetitionOfAClockedSequence,
     APackageSequenceOnTheClockInForceRepeatedIsLegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(PackageSequenceRepeated("s0"), f);
  EXPECT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(RepetitionOfAClockedSequence,
     EveryFormOnAnotherClockIsReportedInAnInstancedUnitOrGenerateBlock) {
  ExpectReportedInEach(EveryFormOnClk1(), InstancedPlaces);
}

TEST(RepetitionOfAClockedSequence,
     DISABLED_EveryFormOnAnotherClockIsReportedInAPackageOrCompilationUnit) {
  ExpectReportedInEach(EveryFormOnClk1(), DeclarationOnlyPlaces);
}

TEST(RepetitionOfAClockedSequence,
     EveryFormOnTheClockInForceIsLegalInEveryOtherPlace) {
  ExpectAcceptedInEach(EveryFormOnClk0(), InstancedPlaces);
  ExpectAcceptedInEach(EveryFormOnClk0(), DeclarationOnlyPlaces);
}

}  // namespace
