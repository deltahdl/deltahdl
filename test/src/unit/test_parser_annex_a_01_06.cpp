#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

const std::vector<ModuleItem*>& IfaceItems(ParseResult& r) {
  static const std::vector<ModuleItem*> kEmpty;
  if (!r.cu || r.cu->interfaces.empty()) return kEmpty;
  return r.cu->interfaces[0]->items;
}

TEST(InterfaceOrGenerateItem, ModuleCommonItemContinuousAssignAndProcedural) {
  auto r = Parse(
      "interface ifc;\n"
      "  wire w;\n"
      "  assign w = a;\n"
      "  initial x = 0;\n"
      "  always @(*) y = w;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  const auto& items = IfaceItems(r);
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kContAssign));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kAlwaysBlock));
}

TEST(InterfaceOrGenerateItem, ModuleCommonItemElaborationSeverityTask) {
  auto r = Parse(
      "interface ifc;\n"
      "  $error(\"bad\");\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(IfaceItems(r), ModuleItemKind::kElabSystemTask));
}

TEST(InterfaceOrGenerateItem, AttributeInstancePrefixOnModuleCommonItem) {
  auto r = Parse(
      "interface ifc;\n"
      "  (* keep *) assign w = a;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(IfaceItems(r), ModuleItemKind::kContAssign);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->attrs.size(), 1u);
  EXPECT_EQ(item->attrs[0].name, "keep");
}

TEST(ExternTfDeclaration, ExternMethodPrototypeFunction) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern function void f(int x);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(IfaceItems(r), ModuleItemKind::kFunctionDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_extern);
  EXPECT_FALSE(item->is_forkjoin);
}

TEST(ExternTfDeclaration, ExternMethodPrototypeTask) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern task t(int x);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(IfaceItems(r), ModuleItemKind::kTaskDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_extern);
  EXPECT_FALSE(item->is_forkjoin);
}

TEST(ExternTfDeclaration, ExternForkjoinTaskPrototype) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern forkjoin task t();\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(IfaceItems(r), ModuleItemKind::kTaskDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_extern);
  EXPECT_TRUE(item->is_forkjoin);
}

TEST(InterfaceItem, NonAnsiPortDeclarationAndNonPortItem) {
  auto r = Parse(
      "interface ifc(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "  assign b = a;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* iface = r.cu->interfaces[0];
  ASSERT_EQ(iface->ports.size(), 2u);
  EXPECT_EQ(iface->ports[0].direction, Direction::kInput);
  EXPECT_EQ(iface->ports[1].direction, Direction::kOutput);
  EXPECT_TRUE(HasItemOfKind(iface->items, ModuleItemKind::kContAssign));
}

TEST(InterfaceItem, WildcardHeaderBodyPortDeclaration) {
  auto r = Parse(
      "extern interface i(b);\n"
      "interface i(.*);\n"
      "  output b;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 2u);
  ASSERT_EQ(r.cu->interfaces[1]->ports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[1]->ports[0].name, "b");
  EXPECT_EQ(r.cu->interfaces[1]->ports[0].direction, Direction::kOutput);
}

TEST(InterfaceItem, AttributedNonAnsiPortDeclaration) {
  auto r = Parse(
      "interface i(b);\n"
      "  (* tag = 2 *) output b;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_EQ(r.cu->interfaces[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports[0].direction, Direction::kOutput);
  ASSERT_EQ(r.cu->interfaces[0]->ports[0].attrs.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports[0].attrs[0].name, "tag");
}

TEST(NonPortInterfaceItem, TimeprecisionAfterPortDeclarationRejected) {
  auto r = Parse(
      "interface i(b);\n"
      "  output b;\n"
      "  timeprecision 1ps;\n"
      "endinterface\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "timeprecision as a later item requires a "
                            "matching prior declaration in the same time scope",
                            3, "3.14.2.2"));
}

TEST(NonPortInterfaceItem, AttributeBeforeAnItemThatTakesNoneRejected) {
  auto r = Parse(
      "interface i;\n"
      "  (* a *) generate endgenerate\n"
      "  (* b *) timeprecision 1ps;\n"
      "endinterface\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a generate region takes no attribute instance", 2, "A.1.6"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "a timeunits declaration takes no attribute "
                            "instance",
                            3, "A.1.6"));
}

TEST(NonPortInterfaceItem, ModportDeclaration) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic a, b;\n"
      "  modport mp(input a, output b);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "mp");
}

TEST(NonPortInterfaceItem, GenerateRegion) {
  auto r = Parse(
      "interface ifc;\n"
      "  generate\n"
      "    if (1) begin : g end\n"
      "  endgenerate\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(IfaceItems(r), ModuleItemKind::kGenerateIf));
}

TEST(NonPortInterfaceItem, NestedInterfaceDeclaration) {
  auto r = Parse(
      "interface outer;\n"
      "  interface inner; endinterface\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(IfaceItems(r), ModuleItemKind::kNestedModuleDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->nested_module_decl, nullptr);
  EXPECT_EQ(item->nested_module_decl->name, "inner");
  EXPECT_EQ(item->nested_module_decl->decl_kind, ModuleDeclKind::kInterface);
}

TEST(NonPortInterfaceItem, NestedProgramDeclaration) {
  auto r = Parse(
      "interface ifc;\n"
      "  program prg; endprogram\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(IfaceItems(r), ModuleItemKind::kNestedModuleDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->nested_module_decl, nullptr);
  EXPECT_EQ(item->nested_module_decl->decl_kind, ModuleDeclKind::kProgram);
}

TEST(NonPortInterfaceItem, NestedExternInterfaceAndProgramDeclaration) {
  auto r = Parse(
      "interface j;\n"
      "  extern interface k(input logic c);\n"
      "  extern program q(input logic d);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(IfaceItems(r).size(), 2u);
  for (auto* item : IfaceItems(r)) {
    ASSERT_NE(item->nested_module_decl, nullptr);
    EXPECT_TRUE(item->nested_module_decl->is_extern);
  }
  EXPECT_EQ(IfaceItems(r)[0]->nested_module_decl->name, "k");
  EXPECT_EQ(IfaceItems(r)[1]->nested_module_decl->decl_kind,
            ModuleDeclKind::kProgram);
}

TEST(NonPortInterfaceItem, TimeunitsDeclaration) {
  auto r = Parse(
      "interface ifc;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_TRUE(r.cu->interfaces[0]->has_timeunit);
  EXPECT_TRUE(r.cu->interfaces[0]->has_timeprecision);
}

TEST(ExternTfDeclaration, ExternMethodPrototypeMissingSemicolonRejected) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern function void f(int x)\n"
      "endinterface\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endinterface'", 3, "13.4"));
}

TEST(ExternTfDeclaration, ExternForkjoinWithFunctionRejected) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern forkjoin function void f();\n"
      "endinterface\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'task', got 'function'", 2, "13.3"));
}

constexpr const char* kExternOutsideInterface =
    "an extern task or function prototype is an item of an interface";

TEST(ExternTfDeclaration, ErrorExternMethodPrototypeInModuleIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  extern task t(int x);\n"
      "  assign w = a;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, kExternOutsideInterface, 2, "A.1.6"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kContAssign));
}

TEST(ExternTfDeclaration, ErrorExternForkjoinTaskPrototypeInModuleIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  extern forkjoin task t();\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, kExternOutsideInterface, 2, "A.1.6"));
}

TEST(ExternTfDeclaration, ErrorExternMethodPrototypeInProgramIsRejected) {
  auto r = Parse(
      "program p;\n"
      "  extern function void f();\n"
      "  initial x = 0;\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(r.diags, kExternOutsideInterface, 2, "A.1.6"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(ExternTfDeclaration, ErrorExternMethodPrototypeInCheckerIsRejected) {
  auto r = Parse(
      "checker c;\n"
      "  extern function int f(int x);\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(r.diags, kExternOutsideInterface, 2, "A.1.6"));
}

TEST(ExternTfDeclaration, ErrorExternMethodPrototypeInPackageIsRejected) {
  auto r = Parse(
      "package pkg;\n"
      "  extern task t();\n"
      "  int x;\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(r.diags, kExternOutsideInterface, 2, "A.1.6"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kVarDecl));
}

TEST(ExternTfDeclaration,
     ErrorExternMethodPrototypeAtCompilationUnitScopeIsRejected) {
  auto r = Parse(
      "extern forkjoin task t(int x);\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, kExternOutsideInterface, 1, "A.1.6"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

TEST(ExternTfDeclaration, ExternMethodPrototypeInInterfaceGenerateBlock) {
  auto r = Parse(
      "interface ifc;\n"
      "  generate\n"
      "    if (1) begin : g\n"
      "      extern task t();\n"
      "    end\n"
      "  endgenerate\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NonPortInterfaceItem, ErrorSpecifyBlockInInterfaceIsRejected) {
  auto r = Parse(
      "interface ifc;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "  assign w = a;\n"
      "endinterface\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "specify block must appear inside a module declaration", 2,
      "30.3"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(HasItemOfKind(IfaceItems(r), ModuleItemKind::kContAssign));
}

TEST(NonPortInterfaceItem, ErrorSpecparamInInterfaceIsRejected) {
  auto r = Parse(
      "interface ifc;\n"
      "  specparam tRise = 150;\n"
      "endinterface\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "specparam declaration must appear inside a module or a specify block", 2,
      "6.20.5"));
}

TEST(NonPortInterfaceItem, SpecifyBlockAndSpecparamInModuleAreAccepted) {
  auto r = Parse(
      "module m;\n"
      "  specparam tRise = 150;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceItemParsing, ADefparamIsNoInterfaceItem) {
  auto r = Parse(
      "interface ifc;\n"
      "  defparam top.u.P = 2;\n"
      "  if (1) begin : g\n"
      "    defparam top.u.P = 3;\n"
      "  end\n"
      "  logic after;\n"
      "endinterface\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a defparam statement is not an item of an interface", 2,
      "A.1.6"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a defparam statement is not an item of an interface", 4,
      "A.1.6"));
}

TEST(InterfaceItemParsing, AGateIsNoInterfaceItem) {
  auto r = Parse(
      "interface ifc;\n"
      "  wire a, b, y, z;\n"
      "  and g(y, a, b);\n"
      "  if (1) begin : gb\n"
      "    not n(z, a);\n"
      "  end\n"
      "endinterface\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a gate instantiation is not an item of an interface", 3,
      "A.1.6"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a gate instantiation is not an item of an interface", 5,
      "A.1.6"));
}

TEST(InterfaceItemParsing, AModuleTakesADefparamAndAGate) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, y;\n"
      "  defparam top.u.P = 2;\n"
      "  and g(y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExternTfDeclaration, ALifetimeInAPrototypeIsReported) {
  auto r = Parse(
      "interface bus;\n"
      "  extern task automatic put(input int d);\n"
      "  extern forkjoin task static get();\n"
      "  extern function automatic int peek();\n"
      "endinterface\n");
  for (int line : {2, 3, 4}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "a task or function prototype takes no lifetime",
                              line, "A.1.6"));
  }
}

TEST(ExternTfDeclaration, AScopedNameInAPrototypeIsReported) {
  auto r = Parse(
      "interface bus;\n"
      "  extern task b.put(input int d);\n"
      "  extern function int C::peek();\n"
      "endinterface\n");
  for (int line : {2, 3}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "a task or function prototype names its task or "
                              "function with an identifier alone",
                              line, "A.1.6"));
  }
}

TEST(ExternTfDeclaration, AnImplicitResultTypeInAPrototypeIsReported) {
  auto r = Parse(
      "interface bus;\n"
      "  extern function peek(input int a);\n"
      "  extern function [7:0] pop();\n"
      "endinterface\n");
  for (int line : {2, 3}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "an extern function prototype writes its result "
                              "type out, a data type or void",
                              line, "A.1.6"));
  }
}

TEST(ExternTfDeclaration, PrototypesAsA26AndA27WriteThemAreAccepted) {
  auto r = Parse(
      "interface bus;\n"
      "  extern task put(input int d);\n"
      "  extern forkjoin task get();\n"
      "  extern function void poke(input int a);\n"
      "  extern function logic [7:0] top();\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExternTfDeclaration, ATypeReferenceResultInAPrototypeIsAccepted) {
  auto r = Parse(
      "interface bus;\n"
      "  extern function type(int) peek(input int a);\n"
      "  extern function type(byte) pop();\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
