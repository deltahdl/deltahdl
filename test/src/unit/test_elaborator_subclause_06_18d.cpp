#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <string_view>
#include <utility>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_declaration_places.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::initializer_list<std::string_view> kDeclarationScopes = {
    "module",           "interface",      "program", "package",
    "compilation unit", "generate block", "class"};

constexpr std::initializer_list<std::string_view> kEveryTypedefPlace = {
    "module",         "interface", "program",
    "checker",        "package",   "compilation unit",
    "generate block", "class",     "function",
    "task",           "block"};

uint32_t WidthOf(const RtlirDesign* design, std::string_view name) {
  if (design == nullptr || design->top_modules.empty()) return 0;
  for (const auto& v : design->top_modules[0]->variables) {
    if (v.name == name) return v.width;
  }
  return 0;
}

TEST(UserDefinedTypeElaboration, TypedefNamesAnExistingTypeInEveryScope) {
  ExpectCleanIn(kDeclarationScopes,
                "  typedef int intP;\n"
                "  intP a, b;\n");
  ExpectCleanIn({"function", "task", "block"},
                "  typedef int intP;\n"
                "  intP a, b;\n");
}

TEST(UserDefinedTypeElaboration,
     ForwardTypedefDefinedAsItselfIsReportedOnceAtTheDefinition) {
  ExpectReportedOnceIn(kEveryTypedefPlace,
                       "  typedef A;\n"
                       "  typedef A A;\n"
                       "  A v;\n",
                       "typedef 'A' does not resolve to a data type",
                       "typedef A A;", "6.18");
}

TEST(UserDefinedTypeElaboration,
     ForwardTypedefDefinedThroughATwoStepCycleIsReported) {
  ExpectReportedIn(kEveryTypedefPlace,
                   "  typedef A;\n"
                   "  typedef A B;\n"
                   "  typedef B A;\n"
                   "  A v;\n",
                   "typedef 'A' does not resolve to a data type",
                   "typedef B A;", "6.18");
}

TEST(UserDefinedTypeElaboration,
     ForwardTypedefDefinedThroughAThreeStepCycleIsReported) {
  ExpectReportedIn(kEveryTypedefPlace,
                   "  typedef A;\n"
                   "  typedef A B;\n"
                   "  typedef B C;\n"
                   "  typedef C A;\n"
                   "  A v;\n",
                   "typedef 'A' does not resolve to a data type",
                   "typedef C A;", "6.18");
}

TEST(UserDefinedTypeElaboration,
     TypedefNamingAMemberOfACycleIsReportedOnceAtTheCycle) {
  ExpectReportedOnceIn(kEveryTypedefPlace,
                       "  typedef A;\n"
                       "  typedef A B;\n"
                       "  typedef B A;\n"
                       "  typedef B D;\n"
                       "  D v;\n",
                       "typedef 'A' does not resolve to a data type",
                       "typedef B A;", "6.18");
}

TEST(UserDefinedTypeElaboration,
     EachForwardFormDefinedThroughACycleIsReported) {
  for (std::string_view form :
       {"class ", "struct ", "enum ", "union ", "interface class "}) {
    SCOPED_TRACE(form);
    std::string body = "  typedef " + std::string(form) +
                       "A;\n"
                       "  typedef A B;\n"
                       "  typedef B A;\n"
                       "  A v;\n";
    ExpectReportedIn(kEveryTypedefPlace, body,
                     "typedef 'A' does not resolve to a data type",
                     "typedef B A;", "6.18");
  }
}

TEST(UserDefinedTypeElaboration,
     PackageTypedefsNamingEachOtherThroughTheirPackageAreReported) {
  ElabFixture f;
  const std::string kSrc =
      "package p;\n"
      "  typedef p::T2 T1;\n"
      "  typedef p::T1 T2;\n"
      "endpackage\n"
      "module m;\n"
      "  p::T1 v;\n"
      "endmodule\n";
  ElaborateSrc(kSrc, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "declaration of type 'T2' does not precede this reference to it",
      LineHolding(kSrc, "typedef p::T2 T1;"), "6.18"));
}

TEST(UserDefinedTypeElaboration,
     TypedefCycleInAClassNothingSpecializesIsReported) {
  ElabFixture f;
  const std::string kSrc =
      "class C;\n"
      "  typedef B;\n"
      "  typedef B A;\n"
      "  typedef A B;\n"
      "  A v;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n";
  ElaborateSrc(kSrc, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "typedef 'B' does not resolve to a data type",
                            LineHolding(kSrc, "typedef A B;"), "6.18"));
}

TEST(UserDefinedTypeElaboration, ForwardTypedefChainEndingInADataTypeResolves) {
  ExpectCleanIn(kEveryTypedefPlace,
                "  typedef A;\n"
                "  typedef A B;\n"
                "  typedef int A;\n"
                "  B v;\n");
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef A;\n"
      "  typedef A B;\n"
      "  typedef int A;\n"
      "  B v;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(WidthOf(design, "v"), 32u);
}

TEST(UserDefinedTypeElaboration, ForwardClassChainWithoutACycleResolves) {
  ExpectCleanIn(kDeclarationScopes,
                "  typedef class A;\n"
                "  typedef A B;\n"
                "  class A;\n"
                "  endclass\n"
                "  B h;\n");
}

TEST(UserDefinedTypeElaboration, ForwardTypedefResolvesInEveryScope) {
  ExpectCleanIn(kDeclarationScopes,
                "  typedef T;\n"
                "  typedef logic [2:0] T;\n"
                "  T v;\n");
  ExpectCleanIn({"function", "task", "block"},
                "  typedef T;\n"
                "  typedef logic [2:0] T;\n"
                "  T v;\n");
  ExpectCleanIn(kDeclarationScopes,
                "  typedef struct T;\n"
                "  typedef struct packed { logic a; } T;\n"
                "  T v;\n");
}

TEST(UserDefinedTypeElaboration,
     UnresolvedForwardTypedefInADesignElementOrTheUnitIsReported) {
  ExpectReportedIn(
      {"module", "interface", "program", "compilation unit", "generate block"},
      "  typedef T;\n"
      "  int v;\n",
      "forward typedef 'T' is never resolved by a definition in the same "
      "scope",
      "typedef T;", "6.18");
}

TEST(
    UserDefinedTypeElaboration,
    DISABLED_UnresolvedForwardTypedefInAPackageClassSubroutineOrBlockIsReported) {
  ExpectReportedIn({"package", "class", "function", "task", "block"},
                   "  typedef T;\n"
                   "  int v;\n",
                   "forward typedef 'T' is never resolved by a definition in "
                   "the same scope",
                   "typedef T;", "6.18");
}

TEST(UserDefinedTypeElaboration,
     ForwardTypedefNamingAValueInAModuleIsReportedAsUnresolved) {
  ExpectReportedIn({"module"},
                   "  typedef T;\n"
                   "  localparam int T = 1;\n",
                   "forward typedef 'T' is never resolved by a definition in "
                   "the same scope",
                   "typedef T;", "6.18");
}

TEST(UserDefinedTypeElaboration,
     DISABLED_ForwardTypedefNamingAValueElsewhereIsReportedAsUnresolved) {
  ExpectReportedIn({"package", "class", "function"},
                   "  typedef T;\n"
                   "  localparam int T = 1;\n",
                   "forward typedef 'T' is never resolved by a definition in "
                   "the same scope",
                   "typedef T;", "6.18");
}

TEST(UserDefinedTypeElaboration,
     NonconformingDefinitionInADesignElementIsReported) {
  ExpectReportedIn({"module", "interface", "program", "generate block"},
                   "  typedef struct T;\n"
                   "  typedef enum {E0} T;\n"
                   "  T v;\n",
                   "typedef 'T' does not conform to its forward declaration "
                   "as struct",
                   "typedef enum", "6.18");
}

TEST(
    UserDefinedTypeElaboration,
    DISABLED_NonconformingDefinitionInAPackageClassUnitSubroutineOrBlockIsReported) {
  ExpectReportedIn(
      {"package", "class", "compilation unit", "function", "task", "block"},
      "  typedef struct T;\n"
      "  typedef enum {E0} T;\n"
      "  T v;\n",
      "typedef 'T' does not conform to its forward declaration "
      "as struct",
      "typedef enum", "6.18");
}

TEST(UserDefinedTypeElaboration,
     DISABLED_PlainClassDefiningAForwardInterfaceClassIsReported) {
  ExpectReportedIn(kDeclarationScopes,
                   "  typedef interface class I;\n"
                   "  class I;\n"
                   "  endclass\n",
                   "typedef 'I' does not conform to its forward declaration "
                   "as interface class",
                   "  class I;", "6.18");
}

TEST(UserDefinedTypeElaboration, InterfaceClassDefiningAForwardOneIsClean) {
  ExpectCleanIn(kDeclarationScopes,
                "  typedef interface class I;\n"
                "  interface class I;\n"
                "  endclass\n");
}

TEST(UserDefinedTypeElaboration,
     DISABLED_TypeNamedBeforeItsTypedefInAPackageIsReported) {
  ElabFixture f;
  const std::string kSrc =
      "package q;\n"
      "  t_t v;\n"
      "  typedef int t_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import q::*;\n"
      "endmodule\n";
  ElaborateSrc(kSrc, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "declaration of type 't_t' does not precede this reference to it",
      LineHolding(kSrc, "t_t v;"), "6.18"));
}

TEST(UserDefinedTypeElaboration,
     DISABLED_PortTypeNamedBeforeTheModuleTypedefIsReported) {
  ElabFixture f;
  const std::string kSrc =
      "module m(input t_t a);\n"
      "  typedef int t_t;\n"
      "endmodule\n";
  ElaborateSrc(kSrc, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "declaration of type 't_t' does not precede this reference to it", 1,
      "6.18"));
}

TEST(UserDefinedTypeElaboration,
     TypeNamedBeforeItsTypedefInAnInterfaceProgramOrGenerateBlockIsReported) {
  ExpectReportedIn({"interface", "program", "generate block"},
                   "  t_t v;\n"
                   "  typedef int t_t;\n",
                   "declaration of type 't_t' does not precede this reference "
                   "to it",
                   "t_t v;", "6.18");
}

TEST(UserDefinedTypeElaboration,
     DISABLED_TypedefThroughAModuleInstanceIsReported) {
  ElabFixture f;
  const std::string kSrc =
      "module inner;\n"
      "  typedef int data_t;\n"
      "endmodule\n"
      "module outer;\n"
      "  inner i();\n"
      "  typedef i.data_t t;\n"
      "  t x;\n"
      "endmodule\n";
  ElaborateSrc(kSrc, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference 'i.data_t' to a type "
                            "identifier is not allowed",
                            LineHolding(kSrc, "typedef i.data_t"), "6.18"));
}

TEST(UserDefinedTypeElaboration,
     DISABLED_TypedefThroughAnAbsoluteHierarchicalNameIsReported) {
  ElabFixture f;
  const std::string kSrc =
      "module sub;\n"
      "  typedef top.data_t t;\n"
      "  t x;\n"
      "endmodule\n"
      "module top;\n"
      "  typedef int data_t;\n"
      "  sub s();\n"
      "endmodule\n";
  ElaborateSrc(kSrc, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference 'top.data_t' to a type "
                            "identifier is not allowed",
                            LineHolding(kSrc, "typedef top.data_t"), "6.18"));
}

TEST(UserDefinedTypeElaboration, PackageScopedTypeIsNoHierarchicalReference) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package q;\n"
      "  typedef logic [4:0] data_t;\n"
      "endpackage\n"
      "module m;\n"
      "  typedef q::data_t t;\n"
      "  t x;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(WidthOf(design, "x"), 5u);
}

TEST(UserDefinedTypeElaboration,
     InterfacePortTypedefOfATypeTheInterfaceLacksIsReported) {
  ElabFixture f;
  const std::string kSrc =
      "interface intf_i;\n"
      "  typedef int data_t;\n"
      "endinterface\n"
      "module sub(intf_i p);\n"
      "  typedef p.no_such_t t;\n"
      "  t data;\n"
      "endmodule\n"
      "module top;\n"
      "  intf_i i();\n"
      "  sub s(i);\n"
      "endmodule\n";
  ElaborateSrc(kSrc, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interface port 'p' names no type 'no_such_t'",
                            LineHolding(kSrc, "typedef p.no_such_t"), "6.18"));
  ElabFixture g;
  const std::string kGeneric =
      "interface intf_i;\n"
      "  typedef int data_t;\n"
      "endinterface\n"
      "module sub(interface p);\n"
      "  typedef p.data_t ok_t;\n"
      "  typedef p.no_such_t t;\n"
      "  t data;\n"
      "endmodule\n"
      "module top;\n"
      "  intf_i i();\n"
      "  sub s1(i);\n"
      "  sub s2(i);\n"
      "endmodule\n";
  ElaborateSrc(kGeneric, g);
  EXPECT_TRUE(ReportedError(
      g.diag.Diagnostics(), "interface port 'p' names no type 'no_such_t'",
      LineHolding(kGeneric, "typedef p.no_such_t"), "6.18"));
  EXPECT_FALSE(ReportedError(g.diag.Diagnostics(), "names no type",
                             LineHolding(kGeneric, "typedef p.data_t"),
                             "6.18"));
}

TEST(UserDefinedTypeElaboration,
     InterfacePortTypedefThroughANameThatIsNoInterfacePortIsReported) {
  ElabFixture f;
  const std::string kSrc =
      "typedef logic [3:0] word_t;\n"
      "class C; endclass\n"
      "interface intf_i;\n"
      "  typedef int data_t;\n"
      "endinterface\n"
      "module no_port(intf_i p);\n"
      "  typedef q.data_t t_no_port;\n"
      "endmodule\n"
      "module data_in(input logic p);\n"
      "  typedef p.data_t t_data_in;\n"
      "endmodule\n"
      "module data_out(output int p);\n"
      "  typedef p.data_t t_data_out;\n"
      "endmodule\n"
      "module typedef_port(word_t p);\n"
      "  typedef p.data_t t_typedef_port;\n"
      "endmodule\n"
      "module class_port(C p);\n"
      "  typedef p.data_t t_class_port;\n"
      "endmodule\n"
      "module top;\n"
      "  intf_i i();\n"
      "  logic l;\n"
      "  int n;\n"
      "  word_t w;\n"
      "  C c;\n"
      "  no_port u0(i);\n"
      "  data_in u1(l);\n"
      "  data_out u2(n);\n"
      "  typedef_port u3(w);\n"
      "  class_port u4(c);\n"
      "endmodule\n";
  ElaborateSrc(kSrc, f);
  const std::pair<const char*, const char*> kCases[] = {
      {"'q' is not an interface port of 'no_port'", "typedef q.data_t"},
      {"'p' is not an interface port of 'data_in'",
       "typedef p.data_t t_data_in"},
      {"'p' is not an interface port of 'data_out'",
       "typedef p.data_t t_data_out"},
      {"'p' is not an interface port of 'typedef_port'",
       "typedef p.data_t t_typedef_port"},
      {"'p' is not an interface port of 'class_port'",
       "typedef p.data_t t_class_port"},
  };
  for (const auto& [message, marker] : kCases) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                              LineHolding(kSrc, marker), "6.18"))
        << message;
  }
}

TEST(UserDefinedTypeElaboration,
     InterfacePortTypedefOfATypeTheInterfaceDefinesIsAccepted) {
  EXPECT_TRUE(
      ElabOk("interface intf_i;\n"
             "  typedef int data_t;\n"
             "  logic x;\n"
             "  modport mp(input x);\n"
             "endinterface\n"
             "module sub(intf_i p);\n"
             "  typedef p.data_t t;\n"
             "  t data;\n"
             "endmodule\n"
             "module gsub(interface p);\n"
             "  typedef p.data_t t;\n"
             "  t data;\n"
             "endmodule\n"
             "module msub(intf_i.mp p);\n"
             "  typedef p.data_t t;\n"
             "  t data;\n"
             "endmodule\n"
             "module gmsub(interface.mp p);\n"
             "  typedef p.data_t t;\n"
             "  t data;\n"
             "endmodule\n"
             "module top;\n"
             "  intf_i i();\n"
             "  sub s(i);\n"
             "  gsub g1(i);\n"
             "  gsub g2(i);\n"
             "  msub m(i.mp);\n"
             "  gmsub gm(i.mp);\n"
             "endmodule\n"));
}

TEST(UserDefinedTypeElaboration,
     DISABLED_TypedefOfAScopedTypeReferenceIsNoForwardTypedef) {
  for (std::string_view name :
       {"module", "interface", "program", "compilation unit"}) {
    SCOPED_TRACE(name);
    std::string src =
        "package pk;\n"
        "  typedef logic [3:0] PT;\n"
        "endpackage\n"
        "class K2;\n"
        "  typedef logic [5:0] T;\n"
        "endclass\n" +
        InPlace(name,
                "  typedef type(pk::PT) t1;\n"
                "  typedef type(K2::T) t2;\n"
                "  t1 a;\n"
                "  t2 b;\n");
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_FALSE(f.has_errors) << src;
  }
}

TEST(UserDefinedTypeElaboration,
     TypedefOfAScopedTypeReferenceSizesTheVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class K2;\n"
      "  typedef logic [5:0] T;\n"
      "endclass\n"
      "module m;\n"
      "  typedef type(K2::T) t2;\n"
      "  t2 b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(WidthOf(design, "b"), 6u);
}

TEST(UserDefinedTypeElaboration,
     TypeOperatorMayTakeAnIncompleteForwardTypeAsItsPrefix) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef C;\n"
      "  var type(C::T) y;\n"
      "  class C;\n"
      "    typedef logic [5:0] T;\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(WidthOf(design, "y"), 6u);
}

TEST(UserDefinedTypeElaboration,
     TypedefMayTakeAnInterfaceBasedTypedefAsItsPrefix) {
  ElabFixture f;
  ElaborateSrc(
      "class Cc;\n"
      "  typedef logic [2:0] T;\n"
      "endclass\n"
      "interface intf_i;\n"
      "  typedef Cc c_t;\n"
      "endinterface\n"
      "module sub(intf_i p);\n"
      "  typedef p.c_t pc_t;\n"
      "  typedef pc_t::T t;\n"
      "  t x;\n"
      "endmodule\n"
      "module top;\n"
      "  intf_i i();\n"
      "  sub s(i);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
