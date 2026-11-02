#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <format>
#include <initializer_list>
#include <span>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §6.23: the expression a type reference names shall reference no element of
// a dynamic object -- a dynamic array (§7.5), a queue (§7.10) or an
// associative array (§7.8) -- wherever the type reference is written. What
// decides is the type of the value a select is applied to, not where that
// value is declared: a name a procedure, a subroutine's formals or a for loop
// declares, a dimension of a multidimensional array after the first (§7.4.5),
// a member of a structure (§7.2), a property read through a class handle
// (§8.5) and the queue an array locator method gives (§7.12.1) each count.
// Each forbidden form is written beside the nearest allowed one: the dynamic
// object named whole, a fixed-size dimension's element, a member or property
// named whole, and a fixed-size array a procedure declares over a dynamic one
// the module declares of the same name (§6.21).

constexpr std::string_view kReport =
    "type operator argument shall not reference elements of dynamic objects";

// The declarations every case reads, at lines 1 to 6, so that the line the
// case writes is line 7: a class whose properties are a dynamic array, a
// queue, an associative array of each kind of index and a fixed-size array,
// and a structure whose member is a queue.
constexpr std::string_view kPreamble =
    "class hc;\n"
    "  int d[]; int q[$]; int a[int]; int w[*]; int f[2];\n"
    "endclass\n"
    "module m;\n"
    "  typedef struct { int q[$]; } sq_t;\n"
    "  logic r;\n";

constexpr uint32_t kCaseLine = 7;

// What a case declares and the operand its type reference writes.
struct Form {
  std::string_view declarations;
  std::string_view operand;
};

constexpr std::array<Form, 11> kForbiddenForms = {{
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
}};

constexpr std::array<Form, 10> kAllowedForms = {{
    {"int d[];", "d"},
    {"int d[$];", "d"},
    {"int d[int];", "d"},
    {"int fx[2][];", "fx[1]"},
    {"sq_t s;", "s.q"},
    {"hc h;", "h.d"},
    {"hc h;", "h.q"},
    {"hc h;", "h.a"},
    {"hc h;", "h.f[1]"},
}};

// Each place a type reference is written in, one line long, {0} standing for
// the form's declarations and {1} for its operand. A procedure's place is
// written twice: as the type of a declaration it makes, and as an operand of
// a comparison one of its statements writes.
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

// A subroutine's formal is a name the subroutine declares (§13.3), so a
// select of a formal that is a dynamic array, a queue or an associative array
// references an element of a dynamic object, and the formal named whole does
// not.
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

// A for loop's own variable is declared with no unpacked dimension of its own
// (A.6.8), so a variable that is a dynamic array, a queue or an associative
// array is declared with a typedef naming one, which the select is judged
// through.
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

// A procedure's declaration hides the module's of the same name (§6.21), so
// the element of a fixed-size array a procedure declares is allowed though
// the module declares a dynamic array of that name, and the element of a
// dynamic array a procedure declares is forbidden though the module's is of
// fixed size.
constexpr std::array<std::string_view, 7> kProceduralPlaces = {
    kInitialDeclaration,  kInitialStatement, kNestedBlockStatement,
    kForkDeclaration,     kTaskStatement,    kFunctionDeclaration,
    kClassMethodStatement};

std::string WritingBehind(std::string_view module_array, std::string_view place,
                          const Form& form) {
  return std::string(kPreamble) + std::string(module_array) + "\n" +
         Placed(place, form) + "\nendmodule\n";
}

// In each of `places`, written after the module's own declaration of `d` at
// line 7, a fixed-size array of that name declared in the place over the
// module's dynamic array is allowed, and a dynamic array over the module's
// fixed-size array is reported at line 8.
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

// A module instantiated twice is elaborated twice, and the operand it writes
// is still one operand, reported once.
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

// A select written inside another expression is still a select: an element
// of a concatenation (§11.4.12), an argument of a system function (§20.5) and
// the bound of a range an inside operator's set lists (§11.4.13), the last
// a bracketed range with no value of its own to select from.
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

// A variable whose type is a typedef naming a fixed-size array is no dynamic
// object, so an element of it is allowed.
TEST(TypeRefDynamicElementElab, TypedefFixedArrayElementAccepted) {
  EXPECT_TRUE(ElabOk(
      Writing(kModuleDeclaration, {"typedef int fa_t[4]; fa_t d;", "d[0]"})));
}

// A for loop's own variable hides the module's of the same name wherever the
// loop's statements write it, so an element of a loop variable of a
// fixed-size array type is allowed though the module declares a dynamic array
// of that name; a cast's type is no comparison folded away before the module
// is checked.
TEST(TypeRefDynamicElementElab, LoopFixedArrayOverModuleDynamicAccepted) {
  EXPECT_TRUE(ElabOk(WritingBehind(
      "int d[];",
      "{0} initial for (fa_t d = start; r; r = 0) r = type({1})'(1);",
      {"typedef int fa_t[3]; fa_t start;", "d[0]"})));
}

// A class's properties, its own and those it inherits from a class it extends
// (§8.13), are names in scope in its methods that hide the module's of the
// same name (§8.5), {0} standing for the property's declaration.
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

// An interface, a program and a checker each declare names and write type
// references in their own bodies (§25.3, §24.3, §17.7, §17.8), so the rule
// holds there as in a module. A checker's body declares no task, process or
// class (§17.2), and its places are those its body allows: a declaration, a
// function and a generate block. Each is instantiated by a top module.
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

TEST(TypeRefDynamicElementElab, ReportedInEachOtherDesignElement) {
  for (const DesignElement& element : kDesignElements) {
    for (std::string_view place : element.places) {
      for (const Form& form : kForbiddenForms) {
        SCOPED_TRACE(std::string(element.keyword) + ": " + std::string(place) +
                     ": " + std::string(form.operand));
        ElabFixture f;
        ElaborateSrc(WritingIn(element.keyword, place, form), f);
        EXPECT_TRUE(
            ReportedError(f.diag.Diagnostics(), kReport, kCaseLine, "6.23"));
      }
    }
  }
}

TEST(TypeRefDynamicElementElab, AcceptedInEachOtherDesignElement) {
  for (const DesignElement& element : kDesignElements) {
    for (std::string_view place : element.places) {
      for (const Form& form : kAllowedForms) {
        SCOPED_TRACE(std::string(element.keyword) + ": " + std::string(place) +
                     ": " + std::string(form.operand));
        EXPECT_TRUE(ElabOk(WritingIn(element.keyword, place, form)));
      }
    }
  }
}

}  // namespace
