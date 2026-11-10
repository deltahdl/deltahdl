#include <gtest/gtest.h>

#include <initializer_list>
#include <span>
#include <string_view>

#include "helpers_declaration_places.h"

using namespace delta;

namespace {

struct Forbidden {
  std::string_view body;
  std::string_view message;
  std::string_view at;
};

constexpr std::initializer_list<std::string_view> kDesignElements = {
    "module", "interface", "program", "checker", "generate block"};

constexpr std::initializer_list<std::string_view> kOtherScopes = {
    "package", "compilation unit", "class", "function", "task", "block"};

constexpr std::initializer_list<std::string_view> kEveryPlace = {
    "module",         "interface", "program",
    "checker",        "package",   "compilation unit",
    "generate block", "class",     "function",
    "task",           "block"};

void ExpectEachReportedIn(std::initializer_list<std::string_view> names,
                          std::span<const Forbidden> forms) {
  for (const Forbidden& form : forms) {
    SCOPED_TRACE(form.body);
    ExpectReportedIn(names, form.body, form.message, form.at, "6.19");
  }
}

void ExpectEachCleanIn(std::initializer_list<std::string_view> names,
                       std::initializer_list<std::string_view> bodies) {
  for (std::string_view body : bodies) {
    ExpectCleanIn(names, body);
  }
}

constexpr Forbidden kXOrZInATwoStateEnumeration[] = {
    {"  enum {A = 0, B = 'z} v;\n", "x/z value in 2-state enum is illegal",
     "enum {A = 0, B = 'z}"},
    {"  enum bit [1:0] {A = 0, B = 2'bx1} v;\n",
     "x/z value in 2-state enum is illegal", "enum bit [1:0]"},
    {"  enum byte {A = 0, B = 'x} v;\n", "x/z value in 2-state enum is illegal",
     "enum byte"},
    {"  enum shortint unsigned {A = 0, B = 'z} v;\n",
     "x/z value in 2-state enum is illegal", "enum shortint"},
    {"  typedef enum longint {A = 0, B = 'x} e_t;\n",
     "x/z value in 2-state enum is illegal", "typedef enum longint"},
};

TEST(EnumerationElaboration,
     XOrZInATwoStateEnumerationIsReportedInADesignElement) {
  ExpectEachReportedIn(kDesignElements, kXOrZInATwoStateEnumeration);
}

TEST(EnumerationElaboration,
     DISABLED_XOrZInATwoStateEnumerationIsReportedInEveryOtherScope) {
  ExpectEachReportedIn(kOtherScopes, kXOrZInATwoStateEnumeration);
}

TEST(EnumerationElaboration, XOrZInAFourStateEnumerationIsCleanEverywhere) {
  ExpectEachCleanIn(kEveryPlace,
                    {"  enum integer {A = 0, B = 'x, C = 'z} v;\n",
                     "  enum logic [1:0] {A = 0, B = 2'bx1, C = 2'bz0} v;\n",
                     "  enum reg signed [1:0] {A = 0, B = 2'bzx} v;\n",
                     "  typedef enum time {A = 0, B = 'x} e_t;\n"});
}

constexpr Forbidden kUnassignedAfterXOrZ[] = {
    {"  enum integer {A = 0, B = 'x, C} v;\n",
     "unassigned enum member 'C' follows member with x/z value",
     "enum integer"},
    {"  typedef enum logic [1:0] {A, B = 2'bz1, C, D} e_t;\n",
     "unassigned enum member 'C' follows member with x/z value",
     "typedef enum logic"},
};

TEST(EnumerationElaboration,
     UnassignedNameAfterXOrZIsReportedInADesignElement) {
  ExpectEachReportedIn(kDesignElements, kUnassignedAfterXOrZ);
}

TEST(EnumerationElaboration,
     DISABLED_UnassignedNameAfterXOrZIsReportedInEveryOtherScope) {
  ExpectEachReportedIn(kOtherScopes, kUnassignedAfterXOrZ);
}

TEST(EnumerationElaboration, UnassignedNameAfterAKnownValueIsCleanEverywhere) {
  ExpectEachCleanIn(kEveryPlace,
                    {"  enum integer {A = 'x, B = 1, C} v;\n",
                     "  enum logic [1:0] {A = 2'bz0, B = 1, C} v;\n"});
}

constexpr Forbidden kIncrementPastTheMaximum[] = {
    {"  enum bit [1:0] {A = 3, B} v;\n",
     "enum auto-increment exceeds maximum representable value of base type",
     "enum bit [1:0]"},
    {"  enum byte {A = 127, B} v;\n",
     "enum auto-increment exceeds maximum representable value of base type",
     "enum byte"},
    {"  typedef enum bit [0:0] {A, B, C} e_t;\n",
     "enum auto-increment exceeds maximum representable value of base type",
     "typedef enum bit"},
};

TEST(EnumerationElaboration,
     IncrementPastTheMaximumIsReportedInADesignElement) {
  ExpectEachReportedIn(kDesignElements, kIncrementPastTheMaximum);
}

TEST(EnumerationElaboration,
     DISABLED_IncrementPastTheMaximumIsReportedInEveryOtherScope) {
  ExpectEachReportedIn(kOtherScopes, kIncrementPastTheMaximum);
}

TEST(EnumerationElaboration, IncrementReachingTheMaximumIsCleanEverywhere) {
  ExpectEachCleanIn(
      kEveryPlace,
      {"  enum bit [1:0] {A = 2, B} v;\n", "  enum byte {A = 126, B} v;\n",
       "  enum byte unsigned {A = 255, B = 0} v;\n"});
}

constexpr Forbidden kDuplicateValue[] = {
    {"  enum {A = 1, B = 1} v;\n", "duplicate enum member value 1",
     "enum {A = 1"},
    {"  typedef enum {A = 0, B = 7, C, D = 8} e_t;\n",
     "duplicate enum member value 8", "typedef enum"},
};

TEST(EnumerationElaboration, DuplicateValueIsReportedInADesignElement) {
  ExpectEachReportedIn(kDesignElements, kDuplicateValue);
}

TEST(EnumerationElaboration,
     DISABLED_DuplicateValueIsReportedInEveryOtherScope) {
  ExpectEachReportedIn(kOtherScopes, kDuplicateValue);
}

constexpr Forbidden kDuplicateName[] = {
    {"  enum {A, B, A} v;\n", "duplicate enum member name 'A'", "enum {A"},
    {"  typedef enum {A, B, A} e_t;\n", "duplicate enum member name 'A'",
     "typedef enum"},
};

TEST(EnumerationElaboration, DuplicateNameIsReportedInADesignElement) {
  ExpectEachReportedIn(kDesignElements, kDuplicateName);
}

TEST(EnumerationElaboration,
     DISABLED_DuplicateNameIsReportedInEveryOtherScope) {
  ExpectEachReportedIn(kOtherScopes, kDuplicateName);
}

TEST(EnumerationElaboration, DistinctNamesAndValuesAreCleanEverywhere) {
  ExpectEachCleanIn(kEveryPlace, {"  enum {A = 0, B = 7, C, D = 9} v;\n",
                                  "  typedef enum {E, F = 7, G} e_t;\n"});
}

constexpr Forbidden kNameOfAnotherEnumeration[] = {
    {"  enum {A, B} v;\n  enum {C, A} w;\n",
     "enum member name 'A' is already declared in this scope", "enum {C, A}"},
    {"  typedef enum {A, B} e_t;\n  enum {C, A} w;\n",
     "enum member name 'A' is already declared in this scope", "enum {C, A}"},
};

TEST(EnumerationElaboration,
     NameOfAnotherEnumerationIsReportedInADesignElement) {
  ExpectEachReportedIn(kDesignElements, kNameOfAnotherEnumeration);
}

TEST(EnumerationElaboration,
     DISABLED_NameOfAnotherEnumerationIsReportedInEveryOtherScope) {
  ExpectEachReportedIn(kOtherScopes, kNameOfAnotherEnumeration);
}

TEST(EnumerationElaboration,
     OneEnumerationSharedByTwoVariablesIsCleanEverywhere) {
  ExpectEachCleanIn(kEveryPlace, {"  enum {A, B} v, w;\n",
                                  "  typedef enum {C, D} e_t;\n  e_t x, y;\n"});
}

constexpr Forbidden kValueOutsideTheBase[] = {
    {"  enum bit [3:0] {A = 'h10} v;\n",
     "enum member 'A' value 16 is outside the representable range of the base "
     "type",
     "enum bit [3:0]"},
    {"  enum bit [3:0] {A = -1} v;\n",
     "enum member 'A' value -1 is outside the representable range of the base "
     "type",
     "enum bit [3:0]"},
    {"  enum bit signed [3:0] {A = 8} v;\n",
     "enum member 'A' value 8 is outside the representable range of the base "
     "type",
     "enum bit signed"},
    {"  enum bit [3:0] {A = 3'h5} v;\n",
     "enum literal width 3 does not match base type width 4", "enum bit [3:0]"},
    {"  enum bit [3:0] {A = 5'h13} v;\n",
     "enum literal width 5 does not match base type width 4", "enum bit [3:0]"},
};

TEST(EnumerationElaboration, ValueOutsideTheBaseIsReportedInADesignElement) {
  ExpectEachReportedIn(kDesignElements, kValueOutsideTheBase);
}

TEST(EnumerationElaboration,
     DISABLED_ValueOutsideTheBaseIsReportedInEveryOtherScope) {
  ExpectEachReportedIn(kOtherScopes, kValueOutsideTheBase);
}

TEST(EnumerationElaboration, ValueTheBaseHoldsIsCleanEverywhere) {
  ExpectEachCleanIn(kEveryPlace,
                    {"  enum bit signed [3:0] {A = -8, B = 7} v;\n",
                     "  enum bit [3:0] {A = 'hF, B = 0} v;\n",
                     "  enum bit [3:0] {A = 4'h3, B, C = 4'h5} v;\n"});
}

TEST(EnumerationElaboration,
     DISABLED_SizedLiteralFillingASignedBaseIsCastAndClean) {
  ExpectEachCleanIn(kEveryPlace, {"  enum byte {A = 8'hFF, B} v;\n",
                                  "  enum bit signed [3:0] {A = 4'hF, B} v;\n",
                                  "  enum shortint {A = 16'h8000, B} v;\n"});
}

TEST(EnumerationElaboration,
     DISABLED_ValueAfterTheCastIsTheOneCheckedForUniqueness) {
  ExpectReportedIn(kEveryPlace, "  enum byte {A = 8'hFF, B, C = 0} v;\n",
                   "duplicate enum member value 0", "enum byte", "6.19");
}

constexpr Forbidden kBaseTypeNameNotIntegral[] = {
    {"  typedef int t;\n  enum t [3:0] {A, B} v;\n",
     "packed dimension not permitted on enum base type 't' that denotes an "
     "integer_atom_type",
     "enum t"},
    {"  typedef struct packed {int a;} t;\n  enum t {A, B} v;\n",
     "enum base type 't' is not an integer_atom_type or integer_vector_type",
     "enum t"},
    {"  typedef real r;\n  enum r {A, B} v;\n",
     "enum base type 'r' is not an integer_atom_type or integer_vector_type",
     "enum r"},
};

TEST(EnumerationElaboration,
     BaseTypeNameOutsideTheBaseFormsIsReportedInADesignElement) {
  ExpectEachReportedIn(kDesignElements, kBaseTypeNameNotIntegral);
}

TEST(EnumerationElaboration,
     DISABLED_BaseTypeNameOutsideTheBaseFormsIsReportedInEveryOtherScope) {
  ExpectEachReportedIn(kOtherScopes, kBaseTypeNameNotIntegral);
}

TEST(EnumerationElaboration, BaseTypeNameOfAnIntegerTypeIsCleanEverywhere) {
  ExpectEachCleanIn(kEveryPlace,
                    {"  typedef int t;\n  enum t {A, B} v;\n",
                     "  typedef logic t;\n  enum t [3:0] {A, B} v;\n",
                     "  typedef bit [5:0] t;\n  enum t {A, B} v;\n"});
}

constexpr Forbidden kOperandNoConstantMayName[] = {
    {"  const static int K = 7;\n  enum {A = K, B} v;\n",
     "const variable 'K' not allowed in enum named constant value",
     "enum {A = K"},
    {"  enum {A = m.X, B} v;\n",
     "hierarchical name not allowed in enum named constant value",
     "enum {A = m.X"},
};

TEST(EnumerationElaboration,
     ConstVariableOrHierarchicalNameIsReportedInADesignElement) {
  ExpectEachReportedIn(kDesignElements, kOperandNoConstantMayName);
}

TEST(EnumerationElaboration,
     DISABLED_ConstVariableOrHierarchicalNameIsReportedInEveryOtherScope) {
  ExpectEachReportedIn(kOtherScopes, kOperandNoConstantMayName);
}

TEST(EnumerationElaboration, LocalparamOperandIsCleanWhereALocalparamMayBe) {
  ExpectCleanIn(
      {"module", "interface", "program", "package", "compilation unit",
       "generate block", "class", "function", "task", "block"},
      "  localparam int K = 7;\n  enum {A = K, B} v;\n");
}

TEST(EnumerationElaboration, DISABLED_VariableOperandIsReportedEverywhere) {
  ExpectReportedIn(kEveryPlace, "  int k;\n  enum {A = k, B} v;\n",
                   "enum member 'A' value is not a constant expression",
                   "enum {A = k", "6.19");
}

TEST(EnumerationElaboration,
     DISABLED_CallOfAFunctionThatIsNoConstantFunctionIsReported) {
  ExpectReportedIn({"module", "interface", "program", "checker", "package",
                    "compilation unit", "generate block", "class"},
                   "  int k;\n"
                   "  function int g();\n"
                   "    return k;\n"
                   "  endfunction\n"
                   "  enum {A = g(), B} v;\n",
                   "constant function 'g' references identifier 'k'",
                   "enum {A = g()", "13.4.3");
}

TEST(EnumerationElaboration, DISABLED_SpecparamOperandIsReported) {
  ExpectReportedIn({"module"},
                   "  specify\n"
                   "    specparam S = 4;\n"
                   "  endspecify\n"
                   "  enum {A = S, B} v;\n",
                   "enum member 'A' value is not a constant expression",
                   "enum {A = S", "6.19");
}

TEST(EnumerationElaboration, DISABLED_GenvarOperandGivesEachIterationItsValue) {
  ExpectCleanIn({"module", "interface", "program"},
                "  for (genvar g = 0; g < 2; g++) begin : b\n"
                "    enum {A = g + 1, B} v;\n"
                "  end\n");
}

TEST(EnumerationElaboration,
     DISABLED_IncrementPastABaseSizedByAClassConstantIsReported) {
  ExpectReportedIn({"class"},
                   "  localparam int L = 2;\n"
                   "  typedef enum bit [L-1:0] {X = 3, Y} e_t;\n",
                   "enum auto-increment exceeds maximum representable value "
                   "of base type",
                   "typedef enum bit", "6.19");
}

}  // namespace
