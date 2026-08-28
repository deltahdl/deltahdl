#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// package_or_generate_item_declaration alternatives (one observer per alt).
// ---------------------------------------------------------------------------

TEST(PackageItemsParsing, NetDeclaration) {
  auto r = Parse(
      "package p;\n"
      "  wire w;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageItemsParsing, DataDeclaration) {
  auto r = Parse(
      "package p;\n"
      "  int x = 42;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, TaskDeclaration) {
  auto r = Parse(
      "package p;\n"
      "  task do_work();\n"
      "  endtask\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, FunctionDeclaration) {
  auto r = Parse(
      "package p;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kFunctionDecl));
}

TEST(PackageItemsParsing, CheckerInPackage) {
  auto r = Parse(
      "package p;\n"
      "  checker my_chk;\n"
      "  endchecker\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, DpiImport) {
  auto r = Parse(
      "package p;\n"
      "  import \"DPI-C\" function int c_func(int x);\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kDpiImport));
}

TEST(PackageItemsParsing, ExternConstraintDeclInPackage) {
  auto r = Parse(
      "package pkg;\n"
      "  class C;\n"
      "    constraint c1;\n"
      "  endclass\n"
      "  constraint C::c1 { }\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageItemsParsing, InterfaceClassInPackage) {
  auto r = Parse(
      "package p;\n"
      "  interface class IFace;\n"
      "    pure virtual function void work();\n"
      "  endclass\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Out-of-block constructor: the genuine class_constructor_declaration alt
// appearing directly as a package item.
TEST(PackageItemsParsing, PackageItemClassConstructorDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  function MyClass::new(); endfunction\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

// local_parameter_declaration and parameter_declaration alternatives.
TEST(PackageItemsParsing, PackageItemLocalparamDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  localparam int A = 1;\n"
      "  parameter int B = 2;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_GE(r.cu->packages[0]->items.size(), 2u);
}

TEST(PackageItemsParsing, PackageWithParamVerifiesAst) {
  auto r = Parse(
      "package my_pkg;\n"
      "  parameter int WIDTH = 8;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1);
  ASSERT_EQ(r.cu->packages[0]->items.size(), 1);
  EXPECT_EQ(r.cu->packages[0]->items[0]->kind, ModuleItemKind::kParamDecl);
}

TEST(PackageItemsParsing, CovergroupInPackage) {
  auto r = Parse(
      "package p;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// assertion_item_declaration: property and sequence forms.
TEST(PackageItemsParsing, PackageItemAssertionDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  property p; 1; endproperty\n"
      "  sequence s; 1; endsequence\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageItemsParsing, NullItem) {
  auto r = Parse(
      "package p;\n"
      "  ;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, PackageWithClassDecl) {
  auto r = Parse(
      "package cls_pkg;\n"
      "  class transaction;\n"
      "    int addr;\n"
      "  endclass\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kClassDecl));
}

// ---------------------------------------------------------------------------
// package_item alternatives beyond package_or_generate_item_declaration.
// ---------------------------------------------------------------------------

TEST(PackageItemsParsing, PackageTimeunits) {
  auto r = Parse(
      "package p;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// package_export_declaration is its own package_item alternative (the named
// and the *::* wildcard forms), distinct from a DPI export.
TEST(PackageItemsParsing, PackageExportDeclaration) {
  auto r = Parse(
      "package pkg;\n"
      "  export other_pkg::*;\n"
      "  export *::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kExportDecl));
}

// ---------------------------------------------------------------------------
// Integration: every alternative coexisting in one package, including the
// package_export_declaration, timeunits, and anonymous_program alternatives.
// ---------------------------------------------------------------------------

TEST(PackageItemsParsing, AllPackageItemAlternatives) {
  auto r = Parse(
      "package pkg;\n"
      // §3.14.2.2: timeunit/timeprecision shall precede any other items in the
      // time scope, so it leads the package body.
      "  timeunit 1ns;\n"
      "  wire w;\n"
      "  int x;\n"
      "  task t(); endtask\n"
      "  function int f(); return 0; endfunction\n"
      "  checker chk; endchecker\n"
      "  import \"DPI-C\" function void c_fn();\n"
      "  class C; endclass\n"
      "  interface class IC;\n"
      "    pure virtual function void g();\n"
      "  endclass\n"
      "  localparam int A = 1;\n"
      "  parameter int B = 2;\n"
      "  covergroup cg; endgroup\n"
      "  property p; 1; endproperty\n"
      "  ;\n"
      "  export other_pkg::*;\n"
      "  program;\n"
      "    task inner_t(); endtask\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_GE(r.cu->packages[0]->items.size(), 10u);
}

// ---------------------------------------------------------------------------
// anonymous_program ::= program ; { anonymous_program_item } endprogram
// ---------------------------------------------------------------------------

TEST(PackageItemsParsing, AnonymousProgramEmpty) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Every anonymous_program_item alternative: task, function, class,
// interface class, class constructor, covergroup, and the null item.
TEST(PackageItemsParsing, AnonymousProgramAllItemTypes) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    task t(); endtask\n"
      "    function void f(); endfunction\n"
      "    class C; endclass\n"
      "    interface class IC;\n"
      "      pure virtual function void g();\n"
      "    endclass\n"
      "    function MyClass::new(); endfunction\n"
      "    covergroup cg; endgroup\n"
      "    ;\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, MultipleAnonymousPrograms) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    task t1(); endtask\n"
      "  endprogram\n"
      "  program;\n"
      "    task t2(); endtask\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, ErrorAnonymousProgramWithPorts) {
  auto r = Parse(
      "package pkg;\n"
      "  program(input clk);\n"
      "  endprogram\n"
      "endpackage\n");
  // §24.6 owns anonymous_program, whose header is 'program ;' with no port
  // list, so the ';' is demanded there.
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got '('", 2, "24.6"));
}

TEST(PackageItemsParsing, ErrorAnonymousProgramMissingEndprogram) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    task t(); endtask\n"
      "endpackage\n");
  // The body scan runs past 'endpackage' looking for 'endprogram' and reaches
  // the end of the source, which stands on line 5, the line the trailing
  // newline opened.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endprogram', got EOF", 5, "24.6"));
}

TEST(PackageItemsParsing, ErrorAnonymousProgramWithName) {
  auto r = Parse(
      "package pkg;\n"
      "  program named_prog;\n"
      "  endprogram\n"
      "endpackage\n");
  // §24.6 owns anonymous_program, whose header is 'program ;' with no name.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got identifier", 2, "24.6"));
}

// ---------------------------------------------------------------------------
// A.1.11 closes anonymous_program_item to task_declaration,
// function_declaration, class_declaration, interface_class_declaration,
// covergroup_declaration, class_constructor_declaration and the null item `;`.
// A closed set is tested by what it excludes, so each case below writes one
// kind the production leaves out. Every one of them is a
// package_or_generate_item_declaration, which A.1.11 admits as a package_item
// and not as an anonymous_program_item, so the surrounding package would take
// it were the program not there.
// ---------------------------------------------------------------------------

// The report FilterAnonymousProgramItems in src/parser/parser.cpp writes and
// the clause it names as the rule. Both stand here rather than in each case
// that reads them, so a rewording at the emission site is one edit here.
// A.1.11 is the clause because it is the production that closes the set; §24.6
// states the name-space rule instead, and §24.3 the syntax of a named
// program_declaration, whose Syntax 24-1 reproduces this production labelled
// as an excerpt from Annex A.
constexpr std::string_view kExcludedItemMessage =
    "an anonymous program may contain only task, function, class, interface "
    "class, covergroup, and class constructor declarations";
constexpr std::string_view kExcludedItemSubclause = "A.1.11";

// The line the item handed to ExpectAnonymousProgramExcludes stands on.
constexpr uint32_t kExcludedItemLine = 3;

// Whether a package holding one anonymous program whose whole body is `item`
// rejects it under A.1.11, and whether the package came away declaring
// nothing. `item` carries its own terminator and holds to one line, so the
// report stands on kExcludedItemLine of the source composed here.
//
// The second claim is the one the report alone does not make. §24.6 has an
// anonymous program declare its items in the surrounding package's name space
// rather than in a scope of its own, so an excluded item the parser kept would
// be an item the package declares -- a parameter or a typedef that collides
// with one written outside the program, or an initial procedure the package
// carries and nothing runs.
void ExpectAnonymousProgramExcludes(const std::string& item) {
  auto r = Parse("package pkg;\n  program;\n    " + item +
                 "\n  endprogram\nendpackage\n");
  EXPECT_TRUE(ReportedError(r.diags, kExcludedItemMessage, kExcludedItemLine,
                            kExcludedItemSubclause));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(r.cu->packages[0]->items.empty());
}

// net_declaration is a package_or_generate_item_declaration and no
// anonymous_program_item.
TEST(PackageItemsParsing, ErrorAnonymousProgramWithNetDecl) {
  ExpectAnonymousProgramExcludes("wire w;");
}

// data_declaration is a package_or_generate_item_declaration and no
// anonymous_program_item.
TEST(PackageItemsParsing, ErrorAnonymousProgramWithDataDecl) {
  ExpectAnonymousProgramExcludes("int x;");
}

// An initial_construct is a non_port_program_item of a named
// program_declaration (Syntax 24-1) and no anonymous_program_item. An
// anonymous program declares no scope of its own (§24.6), so an initial
// procedure kept here becomes a procedure of the package, which nothing
// elaborates and nothing runs.
TEST(PackageItemsParsing, ErrorAnonymousProgramWithInitialBlock) {
  ExpectAnonymousProgramExcludes("initial begin end");
}

// parameter_declaration is a package_or_generate_item_declaration and no
// anonymous_program_item. It carries its value because footnote 22 to Syntax
// 6-6 in §6.20.1 permits the constant_param_expression to be omitted only
// inside a parameter_port_list, so A.1.11's is the only rule this source
// breaks.
TEST(PackageItemsParsing, ErrorAnonymousProgramWithParameterDecl) {
  ExpectAnonymousProgramExcludes("parameter int anon_p = 1;");
}

// A typedef is a data_declaration (A.2.1.3), hence a
// package_or_generate_item_declaration and no anonymous_program_item.
TEST(PackageItemsParsing, ErrorAnonymousProgramWithTypedef) {
  ExpectAnonymousProgramExcludes("typedef int anon_int_t;");
}

// A module_instantiation is a module_or_generate_item and no
// anonymous_program_item; A.1.11 does not admit it even as a package_item.
// The parser reads `m u0();` as a hierarchical_instance from its shape alone,
// because A.4.1.1 makes the port-connection list mandatory, so no
// module_declaration is needed above it to reach that item kind.
TEST(PackageItemsParsing, ErrorAnonymousProgramWithModuleInst) {
  ExpectAnonymousProgramExcludes("m u0();");
}

// One rule reported once per breach, and the clause it names is the same for
// both kinds: the citation belongs to A.1.11's item set rather than to
// whichever kind the source wrote. The two items stand on different lines so
// that the two reports are told apart by where the source broke the rule.
TEST(PackageItemsParsing,
     AnonymousProgramExcludedItemsBothCiteTheGrammarClause) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    wire w;\n"
      "    initial begin end\n"
      "  endprogram\n"
      "endpackage\n");
  EXPECT_TRUE(
      ReportedError(r.diags, kExcludedItemMessage, 3, kExcludedItemSubclause));
  EXPECT_TRUE(
      ReportedError(r.diags, kExcludedItemMessage, 4, kExcludedItemSubclause));
}

}  // namespace
