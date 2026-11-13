#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string Involving(const std::string& name) {
  return "cyclic dependency among named sequences involving \"" + name + "\"";
}

uint32_t DeclLine(const std::string& src, const std::string& name) {
  uint32_t line = LineHolding(src, "sequence " + name + "(");
  return line != 0 ? line : LineHolding(src, "sequence " + name + ";");
}

struct CycleCase {
  std::string form;
  std::string outside;
  std::string items;
  std::vector<std::string> on_cycle;
};

std::string CycleSource(const CycleCase& c) {
  return c.outside +
         "module m;\n"
         "  bit clk, a, b;\n"
         "  " +
         c.items +
         "\n"
         "endmodule\n";
}

void ExpectCycle(const CycleCase& c) {
  SCOPED_TRACE(c.form);
  const std::string kSrc = CycleSource(c);
  ElabFixture f;
  ElaborateSrc(kSrc, f);
  for (const auto& name : c.on_cycle) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), Involving(name),
                              DeclLine(kSrc, name), "16.8"))
        << name;
  }
}

void ExpectNoCycle(const CycleCase& c) {
  SCOPED_TRACE(c.form);
  ElabFixture f;
  ElaborateSrc(CycleSource(c), f);
  for (const auto& diag : f.diag.Diagnostics()) {
    EXPECT_EQ(diag.message.find("cyclic dependency"), std::string::npos)
        << diag.message;
  }
}

const char kPair[] =
    "sequence s1(x); a ##1 x; endsequence\n"
    "  sequence s2(y); b ##1 y; endsequence\n  ";

std::string WithPair(const std::string& items) { return kPair + items; }

std::vector<CycleCase> DeclarationCycles() {
  return {
      {"an actual of an instance in a declaration",
       "",
       "sequence s3(x); a ##1 x; endsequence\n"
       "  sequence s4; a ##1 s3(s4); endsequence",
       {"s3", "s4"}},
      {"an instance with itself in its actual",
       "",
       WithPair("sequence t; s1(s1(a)); endsequence"),
       {"s1"}},
      {"nested actuals",
       "",
       WithPair("sequence t; s1(s2(s1(a))); endsequence"),
       {"s1", "s2"}},
      {"a matched actual",
       "",
       WithPair("sequence s5; @(posedge clk) s1(s5.matched); endsequence"),
       {"s1", "s5"}},
      {"a triggered actual",
       "",
       WithPair("sequence s5; @(posedge clk) s1(s5.triggered); endsequence"),
       {"s1", "s5"}},
      {"a clocking-event formal",
       "",
       "sequence se(ev); @(ev) a; endsequence\n"
       "  sequence w; se(w); endsequence",
       {"se", "w"}},
      {"a package-scoped instance",
       "package pk;\n  sequence s1(x); x; endsequence\nendpackage\n",
       "sequence s6; pk::s1(s6); endsequence",
       {"s6"}},
      {"two property declarations",
       "",
       WithPair("property p1; s1(s2(b)); endproperty\n"
                "  property p2; s2(s1(a)); endproperty"),
       {"s1", "s2"}},
      {"named binding",
       "",
       WithPair("sequence t; s1(.x(s2(.y(b)))) ##1 s2(.y(s1(.x(a)))); "
                "endsequence"),
       {"s1", "s2"}}};
}

TEST(SequenceCycle, ADeclarationsEdgesCloseACycle) {
  for (const auto& c : DeclarationCycles()) ExpectCycle(c);
}

const char kAssertedPair[] =
    "a1: assert property (@(posedge clk) s1(s2(b)));\n"
    "  a2: assert property (@(posedge clk) s2(s1(a)));";

std::vector<CycleCase> InstanceCycles() {
  return {{"two assertions", "", WithPair(kAssertedPair), {"s1", "s2"}},
          {"one assertion with nested actuals",
           "",
           WithPair("assert property (@(posedge clk) s1(s2(s1(a))));"),
           {"s1", "s2"}},
          {"one assertion with itself in its actual",
           "",
           WithPair("assert property (@(posedge clk) s1(s1(a)));"),
           {"s1"}},
          {"an assertion and a declaration",
           "",
           WithPair("assert property (@(posedge clk) s1(s2(b)));\n"
                    "  sequence t; s2(s1(a)); endsequence"),
           {"s1", "s2"}},
          {"a cover and an assume",
           "",
           WithPair("cover property (@(posedge clk) s1(s2(b)));\n"
                    "  assume property (@(posedge clk) s2(s1(a)));"),
           {"s1", "s2"}},
          {"procedural assertions",
           "",
           WithPair("initial assert property (@(posedge clk) s1(s2(b)));\n"
                    "  always @(posedge clk) assert property (s2(s1(a)));"),
           {"s1", "s2"}},
          {"two expect statements",
           "",
           WithPair("initial begin\n"
                    "    expect (@(posedge clk) s1(s2(b)));\n"
                    "    expect (@(posedge clk) s2(s1(a)));\n"
                    "  end"),
           {"s1", "s2"}},
          {"two event controls",
           "",
           WithPair("initial begin @(s1(s2(b))); @(s2(s1(a))); end"),
           {"s1", "s2"}},
          {"named binding in assertions",
           "",
           WithPair("assert property (@(posedge clk) s1(.x(s2(.y(b)))));\n"
                    "  assert property (@(posedge clk) s2(.y(s1(.x(a)))));"),
           {"s1", "s2"}}};
}

TEST(SequenceCycle, DISABLED_AnInstanceOutsideADeclarationAddsItsEdges) {
  for (const auto& c : InstanceCycles()) ExpectCycle(c);
}

std::string InterfaceHolding(const std::string& body) {
  return "interface ifc;\n  bit clk, a, b;\n  " + body + "\nendinterface\n";
}

std::string ProgramHolding(const std::string& body) {
  return "program pg;\n  bit clk, a, b;\n  " + body + "\nendprogram\n";
}

std::string CheckerHolding(const std::string& body) {
  return "checker ck(bit clk, bit a, bit b);\n  " + body + "\nendchecker\n";
}

std::vector<CycleCase> ElsewhereHolding(const std::string& body,
                                        const std::vector<std::string>& on) {
  return {{"interface", InterfaceHolding(body), "ifc i();", on},
          {"program", ProgramHolding(body), "pg p();", on},
          {"checker", CheckerHolding(body), "ck k(clk, a, b);", on}};
}

CycleCase InAGenerateBlock(const std::string& body,
                           const std::vector<std::string>& on) {
  return {"generate block", "", "if (1) begin : g\n    " + body + "\n  end",
          on};
}

TEST(SequenceCycle, DISABLED_EveryPlaceReportsAnAssertionCycle) {
  const std::string kBody = WithPair(kAssertedPair);
  for (const auto& c : ElsewhereHolding(kBody, {"s1", "s2"})) ExpectCycle(c);
  ExpectCycle(InAGenerateBlock(kBody, {"s1", "s2"}));
}

const char kBodyCycle[] =
    "sequence c1; a ##1 c2; endsequence\n"
    "  sequence c2; b ##1 c1; endsequence";

std::vector<CycleCase> PackageAndUnit(const std::string& body,
                                      const std::vector<std::string>& on) {
  return {{"package", "package pk;\n  bit a, b;\n  " + body + "\nendpackage\n",
           "", on},
          {"compilation unit", "bit a, b;\n" + body + "\n", "", on}};
}

TEST(SequenceCycle, ABodyCycleIsReportedInAnInterfaceProgramCheckerOrGenerate) {
  for (const auto& c : ElsewhereHolding(kBodyCycle, {"c1", "c2"})) {
    ExpectCycle(c);
  }
  ExpectCycle(InAGenerateBlock(kBodyCycle, {"c1", "c2"}));
}

TEST(SequenceCycle, DISABLED_ABodyCycleIsReportedInAPackageOrTheUnit) {
  for (const auto& c : PackageAndUnit(kBodyCycle, {"c1", "c2"})) {
    ExpectCycle(c);
  }
}

const char kBodyChain[] =
    "sequence c1; a ##1 b; endsequence\n"
    "  sequence c2; b ##1 c1; endsequence";

TEST(SequenceCycle, AnAcyclicGraphIsAccepted) {
  ExpectNoCycle({"a diamond through an actual",
                 "",
                 "sequence s3; a; endsequence\n"
                 "  sequence s1(x); a ##1 x; endsequence\n"
                 "  sequence s2; s1(s3) ##1 s3; endsequence\n"
                 "  sequence d1; s2 ##1 s3; endsequence",
                 {}});
  ExpectNoCycle({"one direction in two assertions",
                 "",
                 WithPair("assert property (@(posedge clk) s1(s2(b)));\n"
                          "  assert property (@(posedge clk) s1(s2(a)));"),
                 {}});
  ExpectNoCycle({"one direction in one assertion",
                 "",
                 WithPair("assert property (@(posedge clk) s1(s2(b)));"),
                 {}});
  for (const auto& c : ElsewhereHolding(kBodyChain, {})) ExpectNoCycle(c);
  for (const auto& c : PackageAndUnit(kBodyChain, {})) ExpectNoCycle(c);
  ExpectNoCycle(InAGenerateBlock(kBodyChain, {}));
}

TEST(SequenceCycle, DISABLED_OnlyTheSequencesOnTheCycleAreNamed) {
  const CycleCase kReaching = {"a sequence reaching a cycle",
                               "",
                               WithPair("sequence t; s1(b) ##1 b; endsequence\n"
                                        "  sequence u; s1(s1(a)); endsequence"),
                               {"s1"}};
  ExpectCycle(kReaching);
  ElabFixture f;
  ElaborateSrc(CycleSource(kReaching), f);
  for (const auto& diag : f.diag.Diagnostics()) {
    EXPECT_EQ(diag.message.find(Involving("t")), std::string::npos);
    EXPECT_EQ(diag.message.find(Involving("u")), std::string::npos);
  }
}

}  // namespace
