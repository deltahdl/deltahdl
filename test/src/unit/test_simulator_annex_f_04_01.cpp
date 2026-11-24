#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

struct Place {
  std::string before;
  std::string inside;
  std::string prefix;
  std::string declared = "1";
  std::string instanced = "0";
};

struct Form {
  std::string declaration;
  std::string instance;
};

Form BodyForm() { return {"KIND s; g; endKIND", "s"}; }

Form DefaultForm() { return {"KIND s(x = g); x; endKIND", "s()"}; }

Form ActualForm() { return {"KIND s(y); y; endKIND", "s(g)"}; }

Form OverrideForm() { return {"KIND s(x = h); x; endKIND", "s(g)"}; }

void ReplaceAll(std::string& text, const std::string& from,
                const std::string& to) {
  for (std::size_t at = text.find(from); at != std::string::npos;
       at = text.find(from, at + to.size())) {
    text.replace(at, from.size(), to);
  }
}

void ExpectCount(const Place& place, const Form& form, int count) {
  for (const char* kind : {"sequence", "property"}) {
    std::string src = place.before +
                      "module t;\n"
                      "  logic clk = 0;\n"
                      "  initial repeat (20) #5 clk = ~clk;\n"
                      "  int n = 0;\n" +
                      place.inside +
                      "  initial #98 $display(\"n=%0d\", n);\n"
                      "endmodule\n";
    ReplaceAll(src, "DECL", form.declaration);
    ReplaceAll(src, "COVER",
               "cover property (@(posedge clk) " + place.prefix +
                   form.instance + ") n++;");
    ReplaceAll(src, "KIND", kind);
    ReplaceAll(src, "DVAL", place.declared);
    ReplaceAll(src, "IVAL", place.instanced);
    SimFixture f;
    std::string out = RunCapture(src, f);
    EXPECT_NE(out.find("n=" + std::to_string(count) + "\n"), std::string::npos)
        << src << out;
  }
}

void ExpectDeclaringScopeRead(Place place, const Form& form) {
  ExpectCount(place, form, 10);
  place.declared = "0";
  place.instanced = "1";
  ExpectCount(place, form, 0);
}

void ExpectInstanceScopeRead(Place place, const Form& form) {
  ExpectCount(place, form, 0);
  place.declared = "0";
  place.instanced = "1";
  ExpectCount(place, form, 10);
}

Place InstancedElement(const std::string& keyword) {
  return {keyword + " sub;\n  bit g = DVAL, h = DVAL;\n  DECL\nend" + keyword +
              "\n",
          "  bit g = IVAL;\n  sub u();\n  COVER\n", "u."};
}

Place PackageScopePlace() {
  return {"package pk;\n  bit g = DVAL, h = DVAL;\n  DECL\nendpackage\n",
          "  bit g = IVAL;\n  COVER\n", "pk::"};
}

Place PackageImportPlace() {
  return {PackageScopePlace().before,
          "  import pk::*;\n  bit g = IVAL;\n  COVER\n", ""};
}

Place UnitPlace() {
  return {"bit g = DVAL, h = DVAL;\nDECL\n", "  bit g = IVAL;\n  COVER\n", ""};
}

Place GeneratePlace() {
  return {"",
          "  bit g = DVAL, h = DVAL;\n  DECL\n"
          "  if (1) begin : gb\n    bit g = IVAL;\n"
          "    COVER\n  end\n",
          ""};
}

Place NamedBlockPlace() {
  return {"",
          "  bit g = DVAL, h = DVAL;\n  DECL\n"
          "  always @(posedge clk) begin : nb\n"
          "    static bit g = IVAL;\n    COVER\n  end\n",
          ""};
}

Place CheckerPlace() {
  return {"",
          "  checker chk;\n    bit g = DVAL, h = DVAL;\n"
          "    DECL\n    if (1) begin : gb\n"
          "      bit g = IVAL;\n      COVER\n    end\n"
          "  endchecker\n  chk c();\n",
          ""};
}

Place OutsideGeneratePlace() {
  return {"",
          "  bit g = IVAL;\n  if (1) begin : gb\n"
          "    bit g = DVAL, h = DVAL;\n    DECL\n"
          "  end\n  COVER\n",
          "gb."};
}

TEST(BodyNames, AnInterfaceInstancesDeclarationReadsTheInterface) {
  ExpectDeclaringScopeRead(InstancedElement("interface"), BodyForm());
}

TEST(BodyNames, DISABLED_AModuleInstancesDeclarationReadsThatModule) {
  ExpectDeclaringScopeRead(InstancedElement("module"), BodyForm());
}

TEST(BodyNames, DISABLED_AProgramInstancesDeclarationReadsTheProgram) {
  ExpectDeclaringScopeRead(InstancedElement("program"), BodyForm());
}

TEST(BodyNames, DISABLED_AScopedPackageDeclarationReadsThePackage) {
  ExpectDeclaringScopeRead(PackageScopePlace(), BodyForm());
}

TEST(BodyNames, DISABLED_AScopedPackageDeclarationReadsANameTheModuleLacks) {
  Place place = PackageScopePlace();
  place.inside = "  COVER\n";
  ExpectCount(place, BodyForm(), 10);
}

TEST(BodyNames, AnImportedPackageDeclarationReadsThePackage) {
  ExpectDeclaringScopeRead(PackageImportPlace(), BodyForm());
}

TEST(BodyNames, DISABLED_ACompilationUnitDeclarationReadsTheUnit) {
  ExpectDeclaringScopeRead(UnitPlace(), BodyForm());
}

TEST(BodyNames, DISABLED_AnInstanceInARedeclaringGenerateBlockReadsTheModule) {
  ExpectDeclaringScopeRead(GeneratePlace(), BodyForm());
}

TEST(BodyNames, AnInstanceInARedeclaringNamedBlockReadsTheModule) {
  ExpectDeclaringScopeRead(NamedBlockPlace(), BodyForm());
}

TEST(BodyNames, DISABLED_AnInstanceInARedeclaringCheckerBlockReadsTheChecker) {
  ExpectDeclaringScopeRead(CheckerPlace(), BodyForm());
}

TEST(BodyNames,
     DISABLED_AGenerateBlocksDeclarationNamedFromOutsideReadsTheBlock) {
  ExpectDeclaringScopeRead(OutsideGeneratePlace(), BodyForm());
}

TEST(DefaultNames, DISABLED_AnInterfaceInstancesDefaultReadsTheInterface) {
  ExpectDeclaringScopeRead(InstancedElement("interface"), DefaultForm());
}

TEST(DefaultNames,
     DISABLED_AnInterfaceInstancesDefaultReadsANameTheModuleLacks) {
  Place place = InstancedElement("interface");
  place.inside = "  sub u();\n  COVER\n";
  ExpectCount(place, DefaultForm(), 10);
}

TEST(DefaultNames, DISABLED_AModuleInstancesDefaultReadsThatModule) {
  ExpectDeclaringScopeRead(InstancedElement("module"), DefaultForm());
}

TEST(DefaultNames, DISABLED_AProgramInstancesDefaultReadsTheProgram) {
  ExpectDeclaringScopeRead(InstancedElement("program"), DefaultForm());
}

TEST(DefaultNames, AScopedPackageDefaultReadsThePackage) {
  ExpectDeclaringScopeRead(PackageScopePlace(), DefaultForm());
}

TEST(DefaultNames, AnImportedPackageDefaultReadsThePackage) {
  ExpectDeclaringScopeRead(PackageImportPlace(), DefaultForm());
}

TEST(DefaultNames, DISABLED_ACompilationUnitDefaultReadsTheUnit) {
  ExpectDeclaringScopeRead(UnitPlace(), DefaultForm());
}

TEST(DefaultNames,
     DISABLED_AnInstanceInARedeclaringGenerateBlockReadsTheModule) {
  ExpectDeclaringScopeRead(GeneratePlace(), DefaultForm());
}

TEST(DefaultNames, AnInstanceInARedeclaringNamedBlockReadsTheModule) {
  ExpectDeclaringScopeRead(NamedBlockPlace(), DefaultForm());
}

TEST(DefaultNames,
     DISABLED_AnInstanceInARedeclaringCheckerBlockReadsTheChecker) {
  ExpectDeclaringScopeRead(CheckerPlace(), DefaultForm());
}

TEST(DefaultNames,
     DISABLED_AGenerateBlocksDefaultNamedFromOutsideReadsTheBlock) {
  ExpectDeclaringScopeRead(OutsideGeneratePlace(), DefaultForm());
}

TEST(DefaultNames, ALocalFormalsDefaultReadsTheModuleNotTheBodysLocal) {
  Place place = {"", "  bit g = DVAL;\n  DECL\n  COVER\n", ""};
  Form form = {
      "KIND s(local input bit f = g); bit g = 0; (f, g = 0) ##0 f; endKIND",
      "s()"};
  ExpectCount(place, form, 10);
}

TEST(ActualNames, AnInterfaceInstancesActualReadsTheModule) {
  ExpectInstanceScopeRead(InstancedElement("interface"), ActualForm());
}

TEST(ActualNames, AnInterfaceInstancesOverridingActualReadsTheModule) {
  ExpectInstanceScopeRead(InstancedElement("interface"), OverrideForm());
}

TEST(ActualNames, DISABLED_AModuleInstancesActualReadsTheInstancingModule) {
  ExpectInstanceScopeRead(InstancedElement("module"), ActualForm());
}

TEST(ActualNames, DISABLED_AProgramInstancesActualReadsTheInstancingModule) {
  ExpectInstanceScopeRead(InstancedElement("program"), ActualForm());
}

TEST(ActualNames, AScopedPackageInstancesActualReadsTheModule) {
  ExpectInstanceScopeRead(PackageScopePlace(), ActualForm());
}

TEST(ActualNames, AnImportedPackageInstancesActualReadsTheModule) {
  ExpectInstanceScopeRead(PackageImportPlace(), ActualForm());
}

TEST(ActualNames, DISABLED_ACompilationUnitInstancesActualReadsTheModule) {
  ExpectInstanceScopeRead(UnitPlace(), ActualForm());
}

TEST(ActualNames, AGenerateBlocksRedeclaredNameIsRead) {
  ExpectInstanceScopeRead(GeneratePlace(), ActualForm());
}

TEST(ActualNames, ANamedBlocksRedeclaredNameIsRead) {
  ExpectInstanceScopeRead(NamedBlockPlace(), ActualForm());
}

TEST(ActualNames, ACheckerBlocksRedeclaredNameIsRead) {
  ExpectInstanceScopeRead(CheckerPlace(), ActualForm());
}

TEST(ActualNames, DISABLED_AGenerateBlocksInstanceFromOutsideReadsTheModule) {
  ExpectInstanceScopeRead(OutsideGeneratePlace(), ActualForm());
}

TEST(ActualNames, ANameSharedWithAnotherFormalIsNotCaptured) {
  Place place = {"", "  bit g = DVAL, h = IVAL;\n  DECL\n  COVER\n", ""};
  ExpectCount(place, {"KIND s(y, g); y && !g; endKIND", "s(g, h)"}, 10);
}

TEST(ActualNames, ANameSharedWithABodyLocalIsNotCaptured) {
  Place place = {"", "  bit g = DVAL;\n  DECL\n  COVER\n", ""};
  ExpectCount(place, {"KIND s(y); bit g; (1, g = 0) ##0 y; endKIND", "s(g)"},
              10);
}

}  // namespace
