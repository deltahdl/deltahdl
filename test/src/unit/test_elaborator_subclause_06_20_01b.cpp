#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kMissingValue =
    "has no default value and no override at instantiation";

bool HasTopNamed(const RtlirDesign* design, std::string_view name) {
  for (const auto* m : design->top_modules) {
    if (m->name == name) return true;
  }
  return false;
}

size_t CountReports(const ElabFixture& f, std::string_view message) {
  size_t count = 0;
  for (const auto& diag : f.diag.Diagnostics()) {
    if (diag.severity == DiagSeverity::kError &&
        diag.message.find(message) != std::string::npos) {
      ++count;
    }
  }
  return count;
}

TEST(NoDefaultParameterElaboration,
     DISABLED_UninstantiatedModuleWithoutADefaultIsNoImplicitTop) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module lib #(parameter int P);\n"
      "endmodule\n"
      "module top;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(HasTopNamed(design, "top"));
  EXPECT_FALSE(HasTopNamed(design, "lib"));
}

TEST(NoDefaultParameterElaboration,
     DISABLED_UninstantiatedProgramWithoutADefaultIsNoImplicitTop) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "program prg #(parameter int P);\n"
      "endprogram\n"
      "module top;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(HasTopNamed(design, "top"));
  EXPECT_FALSE(HasTopNamed(design, "prg"));
}

TEST(NoDefaultParameterElaboration,
     UninstantiatedModuleWithEveryParameterDefaultedIsAnImplicitTop) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module lib #(parameter int P = 1);\n"
      "endmodule\n"
      "module top;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(HasTopNamed(design, "top"));
  EXPECT_TRUE(HasTopNamed(design, "lib"));
}

TEST(NoDefaultParameterElaboration,
     DISABLED_DefparamSuppliesTheValueOfAParameterWithoutADefault) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int P);\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.P = 7;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NoDefaultParameterElaboration,
     OnlyTheInstanceWithoutAnOverrideIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter int P);\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(7)) u0();\n"
      "  child u1();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter 'P' of 'child' has no default value", 1,
                            "6.20.1"));
  EXPECT_EQ(CountReports(f, kMissingValue), 1u);
}

TEST(NoDefaultParameterElaboration,
     InterfaceInstanceWithoutAnOverrideIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc #(parameter int P);\n"
      "endinterface\n"
      "module top;\n"
      "  ifc i();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter 'P' of 'ifc' has no default value", 1,
                            "6.20.1"));
}

TEST(NoDefaultParameterElaboration,
     ProgramInstanceWithoutAnOverrideIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "program prg #(parameter int P);\n"
      "endprogram\n"
      "module top;\n"
      "  prg p();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter 'P' of 'prg' has no default value", 1,
                            "6.20.1"));
}

TEST(NoDefaultParameterElaboration,
     InterfaceAndProgramInstancesWithOverridesAreAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc #(parameter int P);\n"
      "endinterface\n"
      "program prg #(parameter int P);\n"
      "endprogram\n"
      "module top;\n"
      "  ifc #(.P(3)) i();\n"
      "  prg #(4) p();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BodyParameterLocality, DefparamOfABodyParameterUnderAPortListIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module c #(parameter int W = 8);\n"
      "  parameter int P = 1;\n"
      "endmodule\n"
      "module top;\n"
      "  c u();\n"
      "  defparam u.P = 5;\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "defparam cannot override a local parameter", 6,
                            "23.10.1"));
}

TEST(BodyParameterLocality,
     InterfaceBodyParameterUnderAPortListTakesNoOverride) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc #(parameter int W = 1);\n"
      "  parameter int P = 1;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc #(.P(5)) i();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "has no parameter 'P'", 5,
                            "23.10.2.2"));
}

TEST(BodyParameterLocality, ProgramBodyParameterUnderAPortListTakesNoOverride) {
  ElabFixture f;
  ElaborateSrc(
      "program prg #(parameter int W = 1);\n"
      "  parameter int P = 1;\n"
      "endprogram\n"
      "module top;\n"
      "  prg #(.P(5)) p();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "has no parameter 'P'", 5,
                            "23.10.2.2"));
}

TEST(BodyParameterLocality,
     InterfaceAndProgramBodyParametersWithoutAPortListTakeOverrides) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc;\n"
      "  parameter int P = 1;\n"
      "endinterface\n"
      "program prg;\n"
      "  parameter int P = 1;\n"
      "endprogram\n"
      "module top;\n"
      "  ifc #(.P(5)) i();\n"
      "  prg #(.P(6)) p();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

struct ClassPlace {
  std::string_view name;
  std::string_view before_class;
  std::string_view after_class;
  std::string_view prefix;
};

constexpr ClassPlace kClassPlaces[] = {
    {"compilation unit", "", "module top;\n", ""},
    {"package", "package q;\n", "endpackage\nmodule top;\n", "q::"},
    {"module", "module top;\n", "", ""},
    {"nested class", "class O;\n", "endclass\nmodule top;\n", "O::"},
};

constexpr std::string_view kClassWithAPortList =
    "class C #(int W = 1);\n"
    "  parameter int P = 2;\n"
    "  parameter type T = int;\n"
    "endclass\n";

constexpr std::string_view kClassWithoutAPortList =
    "class C;\n"
    "  parameter int P = 2;\n"
    "endclass\n";

std::string ClassSource(const ClassPlace& place, std::string_view cls,
                        std::string_view specialization) {
  return std::string(place.before_class) + std::string(cls) +
         std::string(place.after_class) + "  " + std::string(place.prefix) +
         "C " + std::string(specialization) + " c;\nendmodule\n";
}

void ExpectSpecializationReported(std::string_view cls,
                                  std::string_view specialization,
                                  std::string_view message,
                                  std::string_view subclause) {
  for (const auto& place : kClassPlaces) {
    SCOPED_TRACE(place.name);
    ElabFixture f;
    std::string src = ClassSource(place, cls, specialization);
    ElaborateSrc(src, f, "top");
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                              LineHolding(src, " c;"), subclause));
  }
}

TEST(BodyParameterLocality,
     DISABLED_NamedOverrideOfABodyValueParameterIsReportedInEveryPlace) {
  ExpectSpecializationReported(kClassWithAPortList, "#(.P(5))",
                               "class 'C' has no parameter 'P'", "23.10.2.2");
}

TEST(BodyParameterLocality,
     DISABLED_NamedOverrideOfABodyTypeParameterIsReportedInEveryPlace) {
  ExpectSpecializationReported(kClassWithAPortList, "#(.T(byte))",
                               "class 'C' has no parameter 'T'", "23.10.2.2");
}

TEST(BodyParameterLocality,
     DISABLED_OrderedValueBeyondThePortListIsReportedInEveryPlace) {
  ExpectSpecializationReported(kClassWithAPortList, "#(4, 5)",
                               "too many positional parameter overrides for "
                               "class 'C': 2 provided, 1 allowed",
                               "23.10.2.1");
}

TEST(BodyParameterLocality,
     DISABLED_NamedOverrideOfAClassWithoutAPortListIsReportedInEveryPlace) {
  ExpectSpecializationReported(kClassWithoutAPortList, "#(.P(3))",
                               "class 'C' has no parameter 'P'", "23.10.2.2");
}

TEST(BodyParameterLocality,
     DISABLED_OrderedOverrideOfAClassWithoutAPortListIsReportedInEveryPlace) {
  ExpectSpecializationReported(kClassWithoutAPortList, "#(3)",
                               "too many positional parameter overrides for "
                               "class 'C': 1 provided, 0 allowed",
                               "23.10.2.1");
}

void ExpectPortOverridesAccepted(const ClassPlace& place) {
  for (std::string_view specialization : {"#(.W(4))", "#(4)"}) {
    SCOPED_TRACE(std::string(place.name) + " " + std::string(specialization));
    ElabFixture f;
    auto* design = ElaborateSrc(
        ClassSource(place, kClassWithAPortList, specialization), f, "top");
    ASSERT_NE(design, nullptr);
    EXPECT_FALSE(f.has_errors);
  }
}

TEST(BodyParameterLocality,
     OverridesOfThePortParameterAreAcceptedOutsideAnotherClass) {
  for (const auto& place : kClassPlaces) {
    if (place.name != "nested class") ExpectPortOverridesAccepted(place);
  }
}

TEST(BodyParameterLocality,
     DISABLED_OverridesOfThePortParameterOfANestedClassAreAccepted) {
  ExpectPortOverridesAccepted(kClassPlaces[3]);
}

}  // namespace
