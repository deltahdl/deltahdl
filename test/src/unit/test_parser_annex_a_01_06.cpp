#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Return the items of the first interface declaration in the parse result.
const std::vector<ModuleItem*>& IfaceItems(ParseResult& r) {
  static const std::vector<ModuleItem*> kEmpty;
  if (!r.cu || r.cu->interfaces.empty()) return kEmpty;
  return r.cu->interfaces[0]->items;
}

// --- interface_or_generate_item ---
// An interface_or_generate_item is either a module_common_item (the set of
// constructs shared with modules, defined in A.1.4) or an extern_tf_declaration.
// These tests observe that the shared module-item parse path is reused for
// interface bodies, so a module_common_item is accepted inside an interface and
// records the same item kind it would in a module.

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

// interface_or_generate_item ::= { attribute_instance } module_common_item | ...
// The production permits a leading run of attribute_instances; the shared
// module-item parse path collects them and attaches them to the resulting item.
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

// --- extern_tf_declaration ---
// extern_tf_declaration ::= extern method_prototype ;
//                         | extern forkjoin task_prototype ;

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

// --- interface_item: port_declaration ; ---
// interface_item ::= port_declaration ; | non_port_interface_item
// A non-ANSI interface lists its port directions in the body as
// port_declarations, which coexist with non_port_interface_items.

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

// --- non_port_interface_item ---
// non_port_interface_item ::= generate_region | interface_or_generate_item
//   | program_declaration | modport_declaration | interface_declaration
//   | timeunits_declaration

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

// --- error conditions / edge cases ---

// extern_tf_declaration ::= extern method_prototype ; — the trailing `;` is
// required after the prototype.
TEST(ExternTfDeclaration, ExternMethodPrototypeMissingSemicolonRejected) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern function void f(int x)\n"
      "endinterface\n");
  EXPECT_TRUE(r.has_errors);
}

// The `forkjoin` keyword form is defined only for a task_prototype
// (extern forkjoin task_prototype ;); pairing it with a function is rejected.
TEST(ExternTfDeclaration, ExternForkjoinWithFunctionRejected) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern forkjoin function void f();\n"
      "endinterface\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
