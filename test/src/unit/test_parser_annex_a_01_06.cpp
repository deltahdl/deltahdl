#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

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
// constructs shared with modules, defined in A.1.4) or an
// extern_tf_declaration. These tests observe that the shared module-item parse
// path is reused for interface bodies, so a module_common_item is accepted
// inside an interface and records the same item kind it would in a module.

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

// interface_or_generate_item ::= { attribute_instance } module_common_item |
// ... The production permits a leading run of attribute_instances; the shared
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
  // §13.4 owns the function declaration whose prototype this is, so the ';'
  // it wants is reported there. `endinterface` is what stands there instead,
  // on line 3.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endinterface'", 3, "13.4"));
}

// The `forkjoin` keyword form is defined only for a task_prototype
// (extern forkjoin task_prototype ;); pairing it with a function is rejected.
TEST(ExternTfDeclaration, ExternForkjoinWithFunctionRejected) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern forkjoin function void f();\n"
      "endinterface\n");
  // `forkjoin` commits the parse to a task declaration, so §13.3 reports the
  // `task` keyword it then wants against the `function` that stands there.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'task', got 'function'", 2, "13.3"));
}

// --- extern_tf_declaration outside an interface ---
// interface_or_generate_item is the one production that admits an
// extern_tf_declaration: A.1.4's module_common_item, A.1.7's
// non_port_program_item, A.1.8's checker_or_generate_item and A.1.11's
// package_item reach task_declaration and function_declaration but no
// prototype, and A.1.2's description admits none at compilation-unit scope.
// §25.7 gives the prototype its purpose: "if the subroutines are defined in a
// module using a hierarchical name, they shall also be declared as extern in
// the interface". Each case below writes the prototype in one of those bodies
// and expects the report at its `extern`, with the body read on past the
// prototype's ';' so that the item after it is still recorded.

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

// At compilation-unit scope the prototype used to be skipped to its ';' with
// nothing said, so the source parsed clean with the prototype gone.
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

// A.4.2's generate_item reaches interface_or_generate_item, so a prototype in
// a generate block of an interface is where A.1.6 puts it. The control the
// rejections above rest on: a rule keyed on the generate block rather than on
// the interface holding it would reject this.
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

// --- non_port_interface_item admits no specify_block or
// specparam_declaration ---
// A.1.4's non_port_module_item lists specify_block and
// { attribute_instance } specparam_declaration; non_port_interface_item lists
// neither. §30.3 has the specify block "defined within a module" and §25.6
// keeps it there when an interface's signals are its terminals, and §6.20.5
// has a specparam "declared inside a module or specify block". Each was
// accepted in an interface body silently and recorded as an item of it.

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

// The control: the same two items in a module body, which A.1.4 admits.
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

}  // namespace
