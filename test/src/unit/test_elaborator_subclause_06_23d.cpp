#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <format>
#include <functional>
#include <initializer_list>
#include <span>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kReport =
    "type operator argument shall not reference elements of dynamic objects";

constexpr std::string_view kPreamble =
    "class hc;\n"
    "  int d[]; int q[$]; int a[int]; int w[*]; int f[2];\n"
    "endclass\n"
    "module m;\n"
    "  typedef struct { int q[$]; } sq_t;\n"
    "  logic r; function automatic sq_t fs(sq_t v); return v; endfunction\n";

constexpr uint32_t kCaseLine = 7;

struct Form {
  std::string_view declarations;
  std::string_view operand;
};

constexpr std::array<Form, 12> kForbiddenForms = {{
    {"int d[];", "d[0]"},
    {"int d[$];", "d[0]"},
    {"int d[int];", "d[0]"},
    {"int fx[2][];", "fx[1][0]"},
    {"int q[$][3];", "q[0][1]"},
    {"sq_t s;", "s.q[0]"},
    {"hc h;", "h.d[0]"},
    {"hc h;", "h.q[0]"},
    {"hc h;", "h.a[0]"},
    {"hc h;", "h.w[0]"},
    {"int arr[4];", "arr.find with (item > 1)[0]"},
    {"sq_t s;", "fs(s).q[0]"},
}};

constexpr std::array<Form, 12> kAllowedForms = {{
    {"int d[];", "d"},
    {"int d[$];", "d"},
    {"int d[int];", "d"},
    {"int fx[2][];", "fx[1]"},
    {"sq_t s;", "s.q"},
    {"hc h;", "h.d"},
    {"hc h;", "h.q"},
    {"hc h;", "h.a"},
    {"hc h;", "h.w"},
    {"hc h;", "h.f[1]"},
    {"int arr[4];", "arr.find with (item > 1)"},
    {"sq_t s;", "fs(s).q"},
}};

constexpr std::string_view kContinuousAssignment =
    "{0} assign r = (type({1}) == type(int));";
constexpr std::string_view kParameterValue =
    "{0} localparam bit L = type({1}) == type(int);";
constexpr std::string_view kModuleDeclaration = "{0} var type({1}) v;";
constexpr std::string_view kInitialDeclaration =
    "initial begin {0} var type({1}) v; end";
constexpr std::string_view kInitialStatement =
    "initial begin {0} bit b; b = (type({1}) == type(int)); end";
constexpr std::string_view kNestedBlockDeclaration =
    "initial begin begin {0} var type({1}) v; end end";
constexpr std::string_view kNestedBlockStatement =
    "initial begin begin {0} bit b; b = (type({1}) == type(int)); end end";
constexpr std::string_view kForkDeclaration =
    "initial fork {0} var type({1}) v; join";
constexpr std::string_view kForkStatement =
    "initial fork {0} bit b; b = (type({1}) == type(int)); join";
constexpr std::string_view kTaskDeclaration =
    "task automatic t(); {0} var type({1}) v; endtask";
constexpr std::string_view kTaskStatement =
    "task automatic t(); {0} bit b; b = (type({1}) == type(int)); endtask";
constexpr std::string_view kFunctionDeclaration =
    "function automatic void f(); {0} var type({1}) v; endfunction";
constexpr std::string_view kFunctionStatement =
    "function automatic void f(); {0} bit b; "
    "b = (type({1}) == type(int)); endfunction";
constexpr std::string_view kClassMethodDeclaration =
    "class c; function void m(); {0} var type({1}) v; endfunction endclass";
constexpr std::string_view kClassMethodStatement =
    "class c; function void m(); {0} bit b; "
    "b = (type({1}) == type(int)); endfunction endclass";
constexpr std::string_view kGenerateDeclaration =
    "if (1) begin : g {0} var type({1}) v; end";
constexpr std::string_view kGenerateStatement =
    "if (1) begin : g {0} initial r = (type({1}) == type(int)); end";
constexpr std::string_view kGenerateContinuousAssignment =
    "if (1) begin : g {0} assign r = (type({1}) == type(int)); end";

std::string Placed(std::string_view place, const Form& form) {
  return std::vformat(place,
                      std::make_format_args(form.declarations, form.operand));
}

std::string Writing(std::string_view place, const Form& form) {
  return std::string(kPreamble) + Placed(place, form) + "\nendmodule\n";
}

void ExpectForbiddenFormsReported(std::string_view place) {
  for (const Form& form : kForbiddenForms) {
    SCOPED_TRACE(form.operand);
    ElabFixture f;
    ElaborateSrc(Writing(place, form), f);
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kReport, kCaseLine, "6.23"));
  }
}

void ExpectAllowedFormsAccepted(std::string_view place) {
  for (const Form& form : kAllowedForms) {
    SCOPED_TRACE(form.operand);
    EXPECT_TRUE(ElabOk(Writing(place, form)));
  }
}

TEST(TypeRefDynamicElementElab, ReportedInAContinuousAssignment) {
  ExpectForbiddenFormsReported(kContinuousAssignment);
}

TEST(TypeRefDynamicElementElab, AcceptedInAContinuousAssignment) {
  ExpectAllowedFormsAccepted(kContinuousAssignment);
}

TEST(TypeRefDynamicElementElab, ReportedInAParameterValue) {
  ExpectForbiddenFormsReported(kParameterValue);
}

TEST(TypeRefDynamicElementElab, AcceptedInAParameterValue) {
  ExpectAllowedFormsAccepted(kParameterValue);
}

TEST(TypeRefDynamicElementElab, ReportedInAModuleDeclaration) {
  ExpectForbiddenFormsReported(kModuleDeclaration);
}

TEST(TypeRefDynamicElementElab, AcceptedInAModuleDeclaration) {
  ExpectAllowedFormsAccepted(kModuleDeclaration);
}

TEST(TypeRefDynamicElementElab, ReportedInAnInitialBlockDeclaration) {
  ExpectForbiddenFormsReported(kInitialDeclaration);
}

TEST(TypeRefDynamicElementElab, AcceptedInAnInitialBlockDeclaration) {
  ExpectAllowedFormsAccepted(kInitialDeclaration);
}

TEST(TypeRefDynamicElementElab, ReportedInAnInitialBlockStatement) {
  ExpectForbiddenFormsReported(kInitialStatement);
}

TEST(TypeRefDynamicElementElab, AcceptedInAnInitialBlockStatement) {
  ExpectAllowedFormsAccepted(kInitialStatement);
}

TEST(TypeRefDynamicElementElab, ReportedInANestedBlockDeclaration) {
  ExpectForbiddenFormsReported(kNestedBlockDeclaration);
}

TEST(TypeRefDynamicElementElab, AcceptedInANestedBlockDeclaration) {
  ExpectAllowedFormsAccepted(kNestedBlockDeclaration);
}

TEST(TypeRefDynamicElementElab, ReportedInANestedBlockStatement) {
  ExpectForbiddenFormsReported(kNestedBlockStatement);
}

TEST(TypeRefDynamicElementElab, AcceptedInANestedBlockStatement) {
  ExpectAllowedFormsAccepted(kNestedBlockStatement);
}

TEST(TypeRefDynamicElementElab, ReportedInAForkDeclaration) {
  ExpectForbiddenFormsReported(kForkDeclaration);
}

TEST(TypeRefDynamicElementElab, AcceptedInAForkDeclaration) {
  ExpectAllowedFormsAccepted(kForkDeclaration);
}

TEST(TypeRefDynamicElementElab, ReportedInAForkStatement) {
  ExpectForbiddenFormsReported(kForkStatement);
}

TEST(TypeRefDynamicElementElab, AcceptedInAForkStatement) {
  ExpectAllowedFormsAccepted(kForkStatement);
}

TEST(TypeRefDynamicElementElab, ReportedInATaskDeclaration) {
  ExpectForbiddenFormsReported(kTaskDeclaration);
}

TEST(TypeRefDynamicElementElab, AcceptedInATaskDeclaration) {
  ExpectAllowedFormsAccepted(kTaskDeclaration);
}

TEST(TypeRefDynamicElementElab, ReportedInATaskStatement) {
  ExpectForbiddenFormsReported(kTaskStatement);
}

TEST(TypeRefDynamicElementElab, AcceptedInATaskStatement) {
  ExpectAllowedFormsAccepted(kTaskStatement);
}

TEST(TypeRefDynamicElementElab, ReportedInAFunctionDeclaration) {
  ExpectForbiddenFormsReported(kFunctionDeclaration);
}

TEST(TypeRefDynamicElementElab, AcceptedInAFunctionDeclaration) {
  ExpectAllowedFormsAccepted(kFunctionDeclaration);
}

TEST(TypeRefDynamicElementElab, ReportedInAFunctionStatement) {
  ExpectForbiddenFormsReported(kFunctionStatement);
}

TEST(TypeRefDynamicElementElab, AcceptedInAFunctionStatement) {
  ExpectAllowedFormsAccepted(kFunctionStatement);
}

TEST(TypeRefDynamicElementElab, ReportedInAClassMethodDeclaration) {
  ExpectForbiddenFormsReported(kClassMethodDeclaration);
}

TEST(TypeRefDynamicElementElab, AcceptedInAClassMethodDeclaration) {
  ExpectAllowedFormsAccepted(kClassMethodDeclaration);
}

TEST(TypeRefDynamicElementElab, ReportedInAClassMethodStatement) {
  ExpectForbiddenFormsReported(kClassMethodStatement);
}

TEST(TypeRefDynamicElementElab, AcceptedInAClassMethodStatement) {
  ExpectAllowedFormsAccepted(kClassMethodStatement);
}

TEST(TypeRefDynamicElementElab, ReportedInAGenerateBlockDeclaration) {
  ExpectForbiddenFormsReported(kGenerateDeclaration);
}

TEST(TypeRefDynamicElementElab, AcceptedInAGenerateBlockDeclaration) {
  ExpectAllowedFormsAccepted(kGenerateDeclaration);
}

TEST(TypeRefDynamicElementElab, ReportedInAGenerateBlockStatement) {
  ExpectForbiddenFormsReported(kGenerateStatement);
}

TEST(TypeRefDynamicElementElab, AcceptedInAGenerateBlockStatement) {
  ExpectAllowedFormsAccepted(kGenerateStatement);
}

TEST(TypeRefDynamicElementElab, ReportedInAGenerateBlockContinuousAssignment) {
  ExpectForbiddenFormsReported(kGenerateContinuousAssignment);
}

TEST(TypeRefDynamicElementElab, AcceptedInAGenerateBlockContinuousAssignment) {
  ExpectAllowedFormsAccepted(kGenerateContinuousAssignment);
}

constexpr std::array<std::string_view, 3> kDynamicFormals = {
    "int d[]", "int d[$]", "int d[int]"};

constexpr std::string_view kFunctionWithFormal =
    "function automatic void f({0}); var type({1}) v; endfunction";
constexpr std::string_view kTaskWithFormal =
    "task automatic t({0}); bit b; b = (type({1}) == type(int)); endtask";

void ExpectFormalSelectReported(std::string_view place) {
  for (std::string_view formal : kDynamicFormals) {
    SCOPED_TRACE(formal);
    ElabFixture f;
    ElaborateSrc(Writing(place, {formal, "d[0]"}), f);
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kReport, kCaseLine, "6.23"));
  }
}

void ExpectFormalAccepted(std::string_view place) {
  for (std::string_view formal : kDynamicFormals) {
    SCOPED_TRACE(formal);
    EXPECT_TRUE(ElabOk(Writing(place, {formal, "d"})));
  }
}

TEST(TypeRefDynamicElementElab, FormalElementReportedInAFunctionDeclaration) {
  ExpectFormalSelectReported(kFunctionWithFormal);
}

TEST(TypeRefDynamicElementElab, FormalAcceptedInAFunctionDeclaration) {
  ExpectFormalAccepted(kFunctionWithFormal);
}

TEST(TypeRefDynamicElementElab, FormalElementReportedInATaskStatement) {
  ExpectFormalSelectReported(kTaskWithFormal);
}

TEST(TypeRefDynamicElementElab, FormalAcceptedInATaskStatement) {
  ExpectFormalAccepted(kTaskWithFormal);
}

constexpr std::array<std::string_view, 3> kLoopArrayTypedefs = {
    "int da_t[]", "int da_t[$]", "int da_t[int]"};

constexpr std::string_view kLoopDeclaration =
    "typedef {0}; da_t start; "
    "initial for (da_t d = start; r; r = 0) begin var type({1}) v; end";
constexpr std::string_view kLoopStatement =
    "typedef {0}; da_t start; initial for (da_t d = start; r; r = 0) "
    "begin bit b; b = (type({1}) == type(int)); end";

void ExpectLoopVariableSelectReported(std::string_view place) {
  for (std::string_view array_typedef : kLoopArrayTypedefs) {
    SCOPED_TRACE(array_typedef);
    ElabFixture f;
    ElaborateSrc(Writing(place, {array_typedef, "d[0]"}), f);
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kReport, kCaseLine, "6.23"));
  }
}

void ExpectLoopVariableAccepted(std::string_view place) {
  for (std::string_view array_typedef : kLoopArrayTypedefs) {
    SCOPED_TRACE(array_typedef);
    EXPECT_TRUE(ElabOk(Writing(place, {array_typedef, "d"})));
  }
}

TEST(TypeRefDynamicElementElab, LoopVariableElementReportedInADeclaration) {
  ExpectLoopVariableSelectReported(kLoopDeclaration);
}

TEST(TypeRefDynamicElementElab, LoopVariableAcceptedInADeclaration) {
  ExpectLoopVariableAccepted(kLoopDeclaration);
}

TEST(TypeRefDynamicElementElab, LoopVariableElementReportedInAStatement) {
  ExpectLoopVariableSelectReported(kLoopStatement);
}

TEST(TypeRefDynamicElementElab, LoopVariableAcceptedInAStatement) {
  ExpectLoopVariableAccepted(kLoopStatement);
}

constexpr std::array<std::string_view, 7> kProceduralPlaces = {
    kInitialDeclaration,  kInitialStatement, kNestedBlockStatement,
    kForkDeclaration,     kTaskStatement,    kFunctionDeclaration,
    kClassMethodStatement};

std::string WritingBehind(std::string_view module_array, std::string_view place,
                          const Form& form) {
  return std::string(kPreamble) + std::string(module_array) + "\n" +
         Placed(place, form) + "\nendmodule\n";
}

void ExpectFixedOverDynamicAccepted(std::span<const std::string_view> places) {
  for (std::string_view place : places) {
    SCOPED_TRACE(place);
    EXPECT_TRUE(
        ElabOk(WritingBehind("int d[];", place, {"int d[3];", "d[0]"})));
  }
}

void ExpectDynamicOverFixedReported(std::span<const std::string_view> places) {
  for (std::string_view place : places) {
    SCOPED_TRACE(place);
    ElabFixture f;
    ElaborateSrc(WritingBehind("int d[3];", place, {"int d[];", "d[0]"}), f);
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kReport, kCaseLine + 1, "6.23"));
  }
}

TEST(TypeRefDynamicElementElab, LocalFixedArrayOverModuleDynamicAccepted) {
  ExpectFixedOverDynamicAccepted(kProceduralPlaces);
}

TEST(TypeRefDynamicElementElab, LocalDynamicArrayOverModuleFixedReported) {
  ExpectDynamicOverFixedReported(kProceduralPlaces);
}

size_t ReportsAcrossTwoInstances(std::string_view body) {
  ElabFixture f;
  ElaborateSrc("module m;\n  int d[];\n  " + std::string(body) +
                   "\nendmodule\n"
                   "module top;\n  m a();\n  m b();\nendmodule\n",
               f);
  return static_cast<size_t>(std::ranges::count_if(
      f.diag.Diagnostics(),
      [](const Diagnostic& diag) { return diag.message == kReport; }));
}

TEST(TypeRefDynamicElementElab, DeclarationReportedOnceForTwoInstances) {
  EXPECT_EQ(ReportsAcrossTwoInstances("var type(d[0]) v;"), 1U);
}

TEST(TypeRefDynamicElementElab, StatementReportedOnceForTwoInstances) {
  EXPECT_EQ(ReportsAcrossTwoInstances(
                "initial begin bit b; b = (type(d[0]) == type(int)); end"),
            1U);
}

constexpr std::array<Form, 3> kNestedForbiddenForms = {{
    {"int d[];", "{d[0], d[0]}"},
    {"int d[];", "$signed(d[0])"},
    {"int d[];", "r inside {[d[0]:1]}"},
}};

TEST(TypeRefDynamicElementElab, NestedElementReported) {
  for (std::string_view place : {kModuleDeclaration, kInitialStatement}) {
    for (const Form& form : kNestedForbiddenForms) {
      SCOPED_TRACE(form.operand);
      ElabFixture f;
      ElaborateSrc(Writing(place, form), f);
      EXPECT_TRUE(
          ReportedError(f.diag.Diagnostics(), kReport, kCaseLine, "6.23"));
    }
  }
}

TEST(TypeRefDynamicElementElab, TypedefFixedArrayElementAccepted) {
  EXPECT_TRUE(ElabOk(
      Writing(kModuleDeclaration, {"typedef int fa_t[4]; fa_t d;", "d[0]"})));
}

TEST(TypeRefDynamicElementElab, LoopFixedArrayOverModuleDynamicAccepted) {
  EXPECT_TRUE(ElabOk(WritingBehind(
      "int d[];",
      "{0} initial for (fa_t d = start; r; r = 0) r = type({1})'(1);",
      {"typedef int fa_t[3]; fa_t start;", "d[0]"})));
}

constexpr std::array<std::string_view, 4> kPropertyPlaces = {
    "class c; {0} function void m(); var type({1}) v; endfunction endclass",
    "class c; {0} function void m(); bit b; "
    "b = (type({1}) == type(int)); endfunction endclass",
    "class pb; {0} endclass class c extends pb; function void m(); "
    "var type({1}) v; endfunction endclass",
    "class pb; {0} endclass class c extends pb; function void m(); bit b; "
    "b = (type({1}) == type(int)); endfunction endclass"};

TEST(TypeRefDynamicElementElab, FixedPropertyOverModuleDynamicAccepted) {
  ExpectFixedOverDynamicAccepted(kPropertyPlaces);
}

TEST(TypeRefDynamicElementElab, DynamicPropertyOverModuleFixedReported) {
  ExpectDynamicOverFixedReported(kPropertyPlaces);
}

struct DesignElement {
  std::string_view keyword;
  std::span<const std::string_view> places;
};

constexpr std::array<std::string_view, 6> kInterfaceAndProgramPlaces = {
    kModuleDeclaration, kInitialStatement,    kTaskDeclaration,
    kFunctionStatement, kGenerateDeclaration, kContinuousAssignment};

constexpr std::array<std::string_view, 3> kCheckerPlaces = {
    kModuleDeclaration, kFunctionDeclaration, kGenerateDeclaration};

constexpr std::array<DesignElement, 3> kDesignElements = {{
    {"interface", kInterfaceAndProgramPlaces},
    {"program", kInterfaceAndProgramPlaces},
    {"checker", kCheckerPlaces},
}};

std::string WritingIn(std::string_view keyword, std::string_view place,
                      const Form& form) {
  std::string src(kPreamble);
  src.replace(src.find("module"), std::string_view("module").size(), keyword);
  return src + Placed(place, form) + "\nend" + std::string(keyword) +
         "\nmodule top;\n  m i();\nendmodule\n";
}

using Writer =
    std::function<std::string(std::string_view place, const Form& form)>;

void ExpectForbiddenFormsReportedIn(
    std::span<const std::string_view> places, const Writer& writing,
    std::span<const Form> forms = kForbiddenForms) {
  for (std::string_view place : places) {
    for (const Form& form : forms) {
      SCOPED_TRACE(writing(place, form));
      ElabFixture f;
      ElaborateSrc(writing(place, form), f);
      EXPECT_TRUE(
          ReportedError(f.diag.Diagnostics(), kReport, kCaseLine, "6.23"));
    }
  }
}

void ExpectAllowedFormsAcceptedIn(std::span<const std::string_view> places,
                                  const Writer& writing,
                                  std::span<const Form> forms = kAllowedForms) {
  for (std::string_view place : places) {
    for (const Form& form : forms) {
      SCOPED_TRACE(writing(place, form));
      EXPECT_TRUE(ElabOk(writing(place, form)));
    }
  }
}

TEST(TypeRefDynamicElementElab, ReportedInEachOtherDesignElement) {
  for (const DesignElement& element : kDesignElements) {
    ExpectForbiddenFormsReportedIn(
        element.places, [&](std::string_view place, const Form& form) {
          return WritingIn(element.keyword, place, form);
        });
  }
}

TEST(TypeRefDynamicElementElab, AcceptedInEachOtherDesignElement) {
  for (const DesignElement& element : kDesignElements) {
    ExpectAllowedFormsAcceptedIn(
        element.places, [&](std::string_view place, const Form& form) {
          return WritingIn(element.keyword, place, form);
        });
  }
}

constexpr std::string_view kPackagePreamble =
    "package p;\n"
    "  class hc;\n"
    "  int d[]; int q[$]; int a[int]; int w[*]; int f[2];\n"
    "  endclass\n"
    "  typedef struct { int q[$]; } sq_t;\n"
    "  logic r; function automatic sq_t fs(sq_t v); return v; endfunction\n";

constexpr std::array<std::string_view, 8> kUnitScopePlaces = {
    kModuleDeclaration,      kParameterValue,      kTaskDeclaration,
    kTaskStatement,          kFunctionDeclaration, kFunctionStatement,
    kClassMethodDeclaration, kClassMethodStatement};

std::string WritingInPackage(std::string_view place, const Form& form) {
  return std::string(kPackagePreamble) + Placed(place, form) +
         "\nendpackage\nmodule top;\nendmodule\n";
}

std::string WritingInCompilationUnit(std::string_view place, const Form& form) {
  std::string src(kPreamble);
  src.erase(src.find("module m;"), std::string_view("module m;").size());
  return src + Placed(place, form) + "\nmodule top;\nendmodule\n";
}

TEST(TypeRefDynamicElementElab, ReportedInAPackage) {
  ExpectForbiddenFormsReportedIn(kUnitScopePlaces, WritingInPackage);
}

TEST(TypeRefDynamicElementElab, AcceptedInAPackage) {
  ExpectAllowedFormsAcceptedIn(kUnitScopePlaces, WritingInPackage);
}

TEST(TypeRefDynamicElementElab, ReportedInTheCompilationUnit) {
  ExpectForbiddenFormsReportedIn(kUnitScopePlaces, WritingInCompilationUnit);
}

TEST(TypeRefDynamicElementElab, AcceptedInTheCompilationUnit) {
  ExpectAllowedFormsAcceptedIn(kUnitScopePlaces, WritingInCompilationUnit);
}

std::span<const Form> PropertyForms(std::span<const Form> forms) {
  return forms.first(forms.size() - 1);
}

std::array<Writer, 3> ClassScopes() {
  return {Writing, WritingInPackage, WritingInCompilationUnit};
}

constexpr std::array<std::string_view, 9> kThisAndSuperPlaces = {
    "class pb; {0} endclass class c extends pb; function void m(); "
    "var type(this.{1}) v; endfunction endclass",
    "class pb; {0} endclass class c extends pb; function void m(); bit b; "
    "b = (type(this.{1}) == type(int)); endfunction endclass",
    "class pb; {0} endclass class c extends pb; function void m(); "
    "var type(super.{1}) v; endfunction endclass",
    "class pb; {0} endclass class c extends pb; function void m(); bit b; "
    "b = (type(super.{1}) == type(int)); endfunction endclass",
    "class pb #(int N = 1); {0} endclass class c extends pb; "
    "function void m(); var type(this.{1}) v; endfunction endclass",
    "class pb #(type T = int); {0} endclass class c extends pb #(byte); "
    "function void m(); var type(super.{1}) v; endfunction endclass",
    "class pb #(int N = 1); {0} endclass class pm extends pb #(3); endclass "
    "class c extends pm; function void m(); var type(this.{1}) v; "
    "endfunction endclass",
    "class pb #(int N = 1); {0} endclass class pm #(int M = 2) extends "
    "pb #(M); endclass class c extends pm #(4); function void m(); "
    "var type(this.{1}) v; endfunction endclass",
    "class pb #(type T = int); {0} endclass class pm #(type U = byte) extends "
    "pb #(U); endclass class c extends pm; function void m(); "
    "var type(super.{1}) v; endfunction endclass"};

TEST(TypeRefDynamicElementElab, PropertyElementThroughThisOrSuperReported) {
  for (const Writer& writing : ClassScopes()) {
    ExpectForbiddenFormsReportedIn(kThisAndSuperPlaces, writing,
                                   PropertyForms(kForbiddenForms));
  }
}

TEST(TypeRefDynamicElementElab, PropertyThroughThisOrSuperAccepted) {
  for (const Writer& writing : ClassScopes()) {
    ExpectAllowedFormsAcceptedIn(kThisAndSuperPlaces, writing,
                                 PropertyForms(kAllowedForms));
  }
}

constexpr std::array<std::string_view, 4> kLocalClassHandlePlaces = {
    "class mk; {0} endclass mk h; var type(h.{1}) v;",
    "class mk; {0} endclass initial begin mk h; bit b; "
    "b = (type(h.{1}) == type(int)); end",
    "if (1) begin : g class mk; {0} endclass mk h; var type(h.{1}) v; end",
    "class mb #(int N = 1); {0} endclass class mk extends mb #(2); endclass "
    "mk h; var type(h.{1}) v;"};

std::array<Writer, 3> ClassDeclaringElements() {
  return {Writing,
          [](std::string_view place, const Form& form) {
            return WritingIn("interface", place, form);
          },
          [](std::string_view place, const Form& form) {
            return WritingIn("program", place, form);
          }};
}

TEST(TypeRefDynamicElementElab, PropertyElementOfALocalClassReported) {
  for (const Writer& writing : ClassDeclaringElements()) {
    ExpectForbiddenFormsReportedIn(kLocalClassHandlePlaces, writing,
                                   PropertyForms(kForbiddenForms));
  }
}

TEST(TypeRefDynamicElementElab, PropertyOfALocalClassAccepted) {
  for (const Writer& writing : ClassDeclaringElements()) {
    ExpectAllowedFormsAcceptedIn(kLocalClassHandlePlaces, writing,
                                 PropertyForms(kAllowedForms));
  }
}

}  // namespace
