#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_sequence_rewrite.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClockRewrite, TransformationProducesUnclockedVersion) {
  auto clocked = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  ASSERT_TRUE(ContainsClock(*clocked));
  auto unclocked = RewriteClockedSequence(*clocked);
  EXPECT_FALSE(ContainsClock(*unclocked));
}

TEST(ClockRewrite, EventOnOrdinarySignalIsIndependent) {
  auto seq = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(ClockEventsAreLocalVariableIndependent(*seq));
}

TEST(ClockRewrite, EventOnDeclaredLocalIsDependent) {
  auto clocked = SeqClock(BoolAtom("v"), SeqBoolean(BoolAtom("a")));
  auto seq = SeqLocalVarDecl("int", "v", clocked);
  EXPECT_FALSE(ClockEventsAreLocalVariableIndependent(*seq));
}

TEST(ClockRewrite, EventOnSampledLocalIsDependent) {
  auto clocked = SeqClock(BoolAtom("v"), SeqBoolean(BoolAtom("a")));
  auto seq = SeqConcat(SeqLocalVarSampling("v"), clocked);
  EXPECT_FALSE(ClockEventsAreLocalVariableIndependent(*seq));
}

TEST(ClockRewrite, EventReadingLocalInsideCompoundConditionIsDependent) {
  auto event = BoolAnd(BoolAtom("clk"), BoolNot(BoolAtom("v")));
  auto clocked = SeqClock(event, SeqBoolean(BoolAtom("a")));
  auto seq = SeqLocalVarDecl("int", "v", clocked);
  EXPECT_FALSE(ClockEventsAreLocalVariableIndependent(*seq));
}

TEST(ClockRewrite, EventOnDistinctNameIsIndependent) {
  auto clocked = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  auto seq = SeqLocalVarDecl("int", "v", clocked);
  EXPECT_TRUE(ClockEventsAreLocalVariableIndependent(*seq));
}

TEST(ClockRewrite, UnclockedSequenceIsVacuouslyIndependent) {
  auto seq = SeqLocalVarDecl(
      "int", "v",
      SeqConcat(SeqLocalVarSampling("v"), SeqBoolean(BoolAtom("v"))));
  EXPECT_TRUE(ClockEventsAreLocalVariableIndependent(*seq));
}

TEST(ClockRewrite, NestedClockEventReadingLocalIsDependent) {
  auto inner = SeqClock(BoolAtom("v"), SeqBoolean(BoolAtom("a")));
  auto outer = SeqClock(BoolAtom("clk"), inner);
  auto seq = SeqLocalVarDecl("int", "v", outer);
  EXPECT_FALSE(ClockEventsAreLocalVariableIndependent(*seq));
}

TEST(ClockRewrite, ClockInOrBranchReadingLocalIsDependent) {
  auto clocked = SeqClock(BoolAtom("v"), SeqBoolean(BoolAtom("a")));
  auto seq =
      SeqLocalVarDecl("int", "v", SeqOr(clocked, SeqBoolean(BoolAtom("b"))));
  EXPECT_FALSE(ClockEventsAreLocalVariableIndependent(*seq));
}

TEST(ClockRewrite, ConstantEventLeavesGuardLocalIndependent) {
  auto clocked = SeqClock(BoolTrue(), SeqBoolean(BoolAtom("v")));
  auto seq =
      SeqLocalVarDecl("int", "v", SeqConcat(SeqLocalVarSampling("v"), clocked));
  EXPECT_TRUE(ClockEventsAreLocalVariableIndependent(*seq));
}

TEST(ClockRewrite, NestedClocksFullyReduceToUnclocked) {
  auto inner = SeqClock(BoolAtom("c2"), SeqBoolean(BoolAtom("b")));
  auto body = SeqConcat(SeqBoolean(BoolAtom("a")), inner);
  auto clocked = SeqClock(BoolAtom("c1"), body);
  ASSERT_TRUE(ContainsClock(*clocked));
  auto unclocked = RewriteClockedSequence(*clocked);
  EXPECT_FALSE(ContainsClock(*unclocked));
}

std::string Replaced(std::string text, const std::string& from,
                     const std::string& to) {
  for (std::size_t at = text.find(from); at != std::string::npos;
       at = text.find(from, at + to.size())) {
    text.replace(at, from.size(), to);
  }
  return text;
}

bool ReportsLocalInClock(const std::string& src, std::uint32_t line) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return ReportedError(
      f.diag.Diagnostics(),
      "local variable \"v\" may not be used in a clocking event expression",
      line, "16.10");
}

bool Accepts(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return f.diag.Diagnostics().empty();
}

void ExpectReportedOnlyWithLocal(const std::string& src, std::uint32_t line) {
  EXPECT_TRUE(ReportsLocalInClock(Replaced(src, "CLK", "v"), line)) << src;
  EXPECT_TRUE(Accepts(Replaced(src, "CLK", "a"))) << src;
}

struct Substitution {
  std::string declared;
  std::string instance;
};

std::string SequenceUser(const Substitution& form) {
  return form.declared +
         "  sequence s;\n    logic v;\n    @(posedge clk) (a, v = b)\n"
         "      ##1 " +
         form.instance + ";\n  endsequence\n";
}

std::string PropertyUser(const Substitution& form) {
  return form.declared +
         "  property p;\n    logic v;\n    @(posedge clk) (a, v = b)\n"
         "      |=> " +
         form.instance + ";\n  endproperty\n";
}

std::string InModule(const std::string& items) {
  return "module m;\n  logic clk, a, b;\n" + items + "endmodule\n";
}

void ExpectSequenceForm(const Substitution& form) {
  ExpectReportedOnlyWithLocal(InModule(SequenceUser(form)), 7);
}

void ExpectPropertyForm(const Substitution& form) {
  ExpectReportedOnlyWithLocal(InModule(PropertyUser(form)), 7);
}

std::string EventSequence() {
  return "  sequence t(event ev, untyped x); @(ev) x; endsequence\n";
}

std::string EventProperty() {
  return "  property t(event ev, untyped x); @(ev) x; endproperty\n";
}

TEST(SubstitutedClock, DISABLED_ALocalAsAnEventActualOfASequence) {
  ExpectSequenceForm({EventSequence(), "t(posedge CLK, b)"});
  ExpectPropertyForm({EventSequence(), "t(posedge CLK, b)"});
}

TEST(SubstitutedClock, DISABLED_ALocalAsAnEventActualOfAProperty) {
  ExpectPropertyForm({EventProperty(), "t(posedge CLK, b)"});
}

TEST(SubstitutedClock, DISABLED_ALocalAsANamedEventActual) {
  ExpectSequenceForm({EventSequence(), "t(.x(b), .ev(posedge CLK))"});
  ExpectPropertyForm({EventProperty(), "t(.x(b), .ev(posedge CLK))"});
}

TEST(SubstitutedClock, DISABLED_ALocalAsAWholeEventActual) {
  ExpectSequenceForm({EventSequence(), "t(CLK, b)"});
  ExpectPropertyForm({EventProperty(), "t(CLK, b)"});
}

TEST(SubstitutedClock, DISABLED_ALocalAsAnUntypedActualUnderAnEdge) {
  ExpectSequenceForm(
      {"  sequence t(untyped c, untyped x); @(posedge c) x; endsequence\n",
       "t(CLK, b)"});
  ExpectPropertyForm(
      {"  property t(untyped c, untyped x); @(posedge c) x; endproperty\n",
       "t(CLK, b)"});
}

TEST(SubstitutedClock, DISABLED_ALocalAsADataTypedActualUnderAnEdge) {
  ExpectSequenceForm(
      {"  sequence t(logic c, untyped x); @(posedge c) x; endsequence\n",
       "t(CLK, b)"});
  ExpectPropertyForm(
      {"  property t(logic c, untyped x); @(posedge c) x; endproperty\n",
       "t(CLK, b)"});
}

TEST(SubstitutedClock, DISABLED_ALocalInAnEventActualsGuard) {
  ExpectSequenceForm({EventSequence(), "t(posedge clk iff CLK, b)"});
  ExpectPropertyForm({EventProperty(), "t(posedge clk iff CLK, b)"});
}

TEST(SubstitutedClock, DISABLED_ALocalAsAnActualInTheInstancesGuard) {
  ExpectSequenceForm(
      {"  sequence t(c, x); @(posedge clk iff c) x; endsequence\n",
       "t(CLK, b)"});
  ExpectPropertyForm(
      {"  property t(c, x); @(posedge clk iff c) x; endproperty\n",
       "t(CLK, b)"});
}

TEST(SubstitutedClock, DISABLED_ALocalAsAnActualInALaterClockOfTheInstance) {
  ExpectSequenceForm(
      {"  sequence t(c, x); @(posedge clk) x ##1 @(posedge c) x; "
       "endsequence\n",
       "t(CLK, b)"});
  ExpectPropertyForm(
      {"  property t(c, x); @(posedge clk) x |=> @(posedge c) x; "
       "endproperty\n",
       "t(CLK, b)"});
}

std::string Declared(const std::string& kind, const std::string& rest) {
  return "  " + kind + " t" + rest + "; end" + kind + "\n";
}

TEST(SubstitutedClock, DISABLED_ALocalAsAnActualInASampledValueFunctionsClock) {
  for (const char* call :
       {"$rose(x, @(posedge c))", "$fell(x, @(posedge c))",
        "$stable(x, @(posedge c))", "$changed(x, @(posedge c))",
        "$past(x, 1, 1, @(posedge c))"}) {
    std::string body = "(c, x); @(posedge clk) ";
    body += call;
    ExpectSequenceForm({Declared("sequence", body), "t(CLK, b)"});
    ExpectPropertyForm({Declared("property", body), "t(CLK, b)"});
  }
}

TEST(SubstitutedClock, DISABLED_ALocalFormalPassedOn) {
  ExpectReportedOnlyWithLocal(
      InModule(EventSequence() + "  sequence s(local input logic v);\n"
                                 "    @(posedge clk) (v == a)\n"
                                 "      ##1 t(posedge CLK, b);\n"
                                 "  endsequence\n"),
      6);
  ExpectReportedOnlyWithLocal(
      InModule(EventProperty() + "  property p(local input logic v);\n"
                                 "    @(posedge clk) (v == a)\n"
                                 "      |=> t(posedge CLK, b);\n"
                                 "  endproperty\n"),
      6);
}

TEST(SubstitutedClock, DISABLED_ALocalPassedThroughAChainOfInstances) {
  ExpectSequenceForm(
      {"  sequence t(event ev, untyped x); @(ev) x; endsequence sequence "
       "mid(c, x); t(posedge c, x); endsequence\n",
       "mid(CLK, b)"});
  ExpectPropertyForm(
      {"  property t(event ev, untyped x); @(ev) x; endproperty property "
       "mid(c, x); t(posedge c, x); endproperty\n",
       "mid(CLK, b)"});
}

TEST(SubstitutedClock, DISABLED_ALocalPassedToAPackagesDeclaration) {
  for (const bool kSequence : {true, false}) {
    const Substitution kForm = {"", "k::t(posedge CLK, b)"};
    const std::string kPackage =
        "package k;\n" + (kSequence ? EventSequence() : EventProperty()) +
        "endpackage\n";
    ExpectReportedOnlyWithLocal(
        kPackage +
            InModule(kSequence ? SequenceUser(kForm) : PropertyUser(kForm)),
        9);
  }
}

void ExpectEverySubstitutionReported(const std::string& open,
                                     const std::string& close) {
  const Substitution kEverySubstitution[] = {
      {"  sequence t(event ev, untyped x); @(ev) x; endsequence\n",
       "t(posedge CLK, b)"},
      {"  sequence t(event ev, untyped x); @(ev) x; endsequence\n",
       "t(posedge clk iff CLK, b)"},
      {"  sequence t(untyped c, x); @(posedge c) x; endsequence\n",
       "t(CLK, b)"},
      {"  sequence t(logic c, untyped x); @(posedge c) x; endsequence\n",
       "t(CLK, b)"},
      {"  sequence t(c, x); @(posedge clk iff c) x; endsequence\n",
       "t(CLK, b)"},
      {"  sequence t(c, x); $rose(x, @(posedge c)); endsequence\n",
       "t(CLK, b)"}};
  for (const auto& form : kEverySubstitution) {
    std::string sequence = open;
    sequence += SequenceUser(form);
    sequence += close;
    ExpectReportedOnlyWithLocal(sequence, 7);
    std::string property = open;
    property += PropertyUser(
        {Replaced(form.declared, "sequence", "property"), form.instance});
    property += close;
    ExpectReportedOnlyWithLocal(property, 7);
  }
}

TEST(SubstitutedClock, DISABLED_EachFormIsReportedInAnInterface) {
  ExpectEverySubstitutionReported("interface i;\n  logic clk, a, b;\n",
                                  "endinterface\n");
}

TEST(SubstitutedClock, DISABLED_EachFormIsReportedInAProgram) {
  ExpectEverySubstitutionReported("program g;\n  logic clk, a, b;\n",
                                  "endprogram\n");
}

TEST(SubstitutedClock, DISABLED_EachFormIsReportedInAChecker) {
  ExpectEverySubstitutionReported("checker c;\n  logic clk, a, b;\n",
                                  "endchecker\nmodule m; c c_i(); endmodule\n");
}

TEST(SubstitutedClock, DISABLED_EachFormIsReportedInAPackage) {
  ExpectEverySubstitutionReported("package k;\n  logic clk, a, b;\n",
                                  "endpackage\nmodule m; endmodule\n");
}

TEST(SubstitutedClock, DISABLED_EachFormIsReportedInTheCompilationUnit) {
  ExpectEverySubstitutionReported("logic clk;\nlogic a, b;\n",
                                  "module m; endmodule\n");
}

TEST(SubstitutedClock, DISABLED_EachFormIsReportedInAGenerateBlock) {
  ExpectEverySubstitutionReported(
      "module m; logic clk, a, b;\n  if (1) begin : g\n", "end endmodule\n");
}

TEST(SubstitutedClock, ALocalReadOutsideTheInstancesClockIsAccepted) {
  EXPECT_TRUE(Accepts(InModule(
      SequenceUser({"  sequence t(c, x); @(posedge c) x; endsequence\n",
                    "t(clk, v == b)"}))));
  EXPECT_TRUE(Accepts(InModule(
      PropertyUser({"  property t(c, x); @(posedge c) x; endproperty\n",
                    "t(clk, v == b)"}))));
}

TEST(SubstitutedClock, ASignalClockBesideALocalValueActualIsAccepted) {
  EXPECT_TRUE(
      Accepts(InModule(SequenceUser({EventSequence(), "t(posedge clk, v)"}))));
  EXPECT_TRUE(
      Accepts(InModule(PropertyUser({EventProperty(), "t(posedge clk, v)"}))));
}

}  // namespace
