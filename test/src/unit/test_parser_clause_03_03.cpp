// §3.3

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §3.3 states that the module — the basic building block — is "enclosed
// between the keywords module and endmodule". Verify the parser accepts a
// declaration that opens with `module` and closes with `endmodule`, and that
// it builds the corresponding ModuleDecl with that exact decl_kind. Observing
// a populated cu->modules entry with kModule confirms ParseModuleDecl
// consumed both bracketing keywords on the success path.
TEST(ModuleEnclosure, ModuleEndmoduleKeywordsBracketDeclaration) {
  auto r = Parse("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_EQ(r.cu->modules[0]->decl_kind, ModuleDeclKind::kModule);
}

// §3.3's enclosure rule binds both ends of the bracket: omitting `endmodule`
// must not parse as a well-formed module. Drive the parser at a source that
// opens `module m;` and ends before `endmodule`; the Expect(kKwEndmodule)
// call inside ParseModuleDecl is the production-code site that observes the
// rule, and it should raise a diagnostic the test sees as has_errors.
TEST(ModuleEnclosure, MissingEndmoduleIsRejected) {
  auto r = Parse("module m;\n");
  EXPECT_TRUE(r.has_errors);
}

// §3.3's bracket holds across the module's body: `endmodule` closes the
// declaration whether the body is empty or carries items. The
// ParseModuleBody loop only terminates at `endmodule` or EOF, so observing
// a clean parse on a module that carries an item proves the loop exited on
// the closing keyword rather than truncating early.
TEST(ModuleEnclosure, EndmoduleClosesModuleWithBody) {
  auto r = Parse("module m; wire w; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_FALSE(r.cu->modules[0]->items.empty());
}

// §3.3's bracket cannot be substituted by body content: a module that
// carries items but never reaches `endmodule` must still be rejected.
// Reaching EOF inside the body drops out of ParseModuleBody on AtEnd(),
// after which Expect(kKwEndmodule) sees EOF and raises the diagnostic.
TEST(ModuleEnclosure, BodyContentDoesNotSubstituteForEndmodule) {
  auto r = Parse("module m; wire w;\n");
  EXPECT_TRUE(r.has_errors);
}

// §3.3 lists "Ports, with port declarations" as a module construct.
// ParseModuleDecl calls ParseParamsPortsAndSemicolon, which fills
// ModuleDecl::ports from the ANSI port list. Observe the parser
// populating that vector from a port-bearing header.
TEST(ModuleItems, PortsWithPortDeclarations) {
  auto r = Parse("module m(input wire a, output logic y); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "y");
}

// §3.3 lists "Data declarations, such as nets, variables, structures,
// and unions" as a module construct. ParseModuleItem falls through to
// ParseDataDeclItem / ParseVarPrefixed for net, variable, struct and
// union declarations. Observe each kind landing as a module item.
TEST(ModuleItems, DataDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  logic v;\n"
      "  struct packed { logic a; logic b; } s;\n"
      "  union packed { logic [7:0] x; logic [7:0] y; } u;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kNetDecl));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kVarDecl));
}

// §3.3 lists "Constant declarations" as a module construct. The module
// item dispatcher routes `parameter` and `localparam` to ParseParamDecl,
// which emits ModuleItemKind::kParamDecl entries. Observe both forms.
TEST(ModuleItems, ConstantDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  parameter WIDTH = 8;\n"
      "  localparam DEPTH = 16;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kParamDecl),
      2u);
}

// §3.3 lists "User-defined type definitions" as a module construct. The
// dispatcher routes `typedef` to ParseTypedef, producing a
// ModuleItemKind::kTypedef item. Observe the parser accepting one inside
// a module body.
TEST(ModuleItems, UserDefinedTypeDefinitions) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kTypedef));
}

// §3.3 lists "Class definitions" as a module construct. The dispatcher
// detects `class` via IsAtClassDecl and emits a ModuleItemKind::kClassDecl
// item built by ParseClassDecl. Observe a nested class landing as a
// module item.
TEST(ModuleItems, ClassDefinitions) {
  auto r = Parse(
      "module m;\n"
      "  class my_class; int val; endclass\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kClassDecl));
}

// §3.3 lists "Imports of declarations from packages" as a module
// construct. ParseModuleItem routes `import` to ParseImportDecl, emitting
// ModuleItemKind::kImportDecl. Observe a package-import statement at
// module-item scope.
TEST(ModuleItems, PackageImports) {
  auto r = Parse(
      "package pkg; parameter int K = 1; endpackage\n"
      "module m;\n"
      "  import pkg::K;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kImportDecl));
}

// §3.3 lists "Subroutine definitions" as a module construct. The
// dispatcher routes `function` to ParseFunctionDecl and `task` to
// ParseTaskDecl, yielding kFunctionDecl / kTaskDecl module items.
// Observe both forms at module-item scope.
TEST(ModuleItems, SubroutineDefinitions) {
  auto r = Parse(
      "module m;\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "  task t(input int x); endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kFunctionDecl));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kTaskDecl));
}

// §3.3 lists "Instantiations of other modules, programs, interfaces,
// checkers, and primitives" as a module construct. The dispatcher routes
// an unknown identifier followed by an instance head to
// ParseModuleInstList (kModuleInst) and routes built-in gate keywords to
// ParseGateInst (kGateInst). Observe both forms landing in the items.
TEST(ModuleItems, ModuleAndPrimitiveInstantiations) {
  auto r = Parse(
      "module sub; endmodule\n"
      "module m;\n"
      "  sub u_sub();\n"
      "  and g(w, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules.size(), 2u);
  auto& items = r.cu->modules[1]->items;
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kModuleInst));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kGateInst));
}

// §3.3 lists "Instantiations of class objects" as a module construct.
// A class-typed variable declaration at module-item scope is the
// instantiation form: ParseVarPrefixed/ParseImplicitTypeOrInst resolves
// the class name as a known type and emits a kVarDecl. Observe the
// declaration landing alongside the class definition.
TEST(ModuleItems, ClassObjectInstantiations) {
  auto r = Parse(
      "module m;\n"
      "  class my_class; int val; endclass\n"
      "  my_class obj;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kClassDecl));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kVarDecl));
}

// §3.3 lists "Continuous assignments" as a module construct. The
// dispatcher routes `assign` to ParseContinuousAssign, emitting one
// ModuleItemKind::kContAssign per LHS. Observe an `assign` statement at
// module-item scope.
TEST(ModuleItems, ContinuousAssignments) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, y;\n"
      "  assign y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kContAssign));
}

// §3.3 lists "Procedural blocks" as a module construct. TryParseProcessBlock
// routes `initial`, `final`, and the `always*` family to their parsers,
// emitting kInitialBlock, kFinalBlock, and the kAlways* kinds. Observe
// each procedural-block form at module-item scope.
TEST(ModuleItems, ProceduralBlocks) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  initial a = 0;\n"
      "  final $display(\"done\");\n"
      "  always @(posedge clk) a <= b;\n"
      "  always_comb b = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kFinalBlock));
  EXPECT_TRUE(HasAlwaysOfKind(items, AlwaysKind::kAlways));
  EXPECT_TRUE(HasAlwaysOfKind(items, AlwaysKind::kAlwaysComb));
}

// §3.3 lists "Generate blocks" as a module construct. The dispatcher
// routes `for`, `if`, `case` (and `generate` regions) at module-item
// scope to ParseGenerateFor/If/Case, emitting kGenerateFor / kGenerateIf
// / kGenerateCase. Observe each generate-block form.
TEST(ModuleItems, GenerateBlocks) {
  auto r = Parse(
      "module m;\n"
      "  parameter N = 2;\n"
      "  genvar i;\n"
      "  for (i = 0; i < N; i = i + 1) begin: g_loop end\n"
      "  if (N > 0) begin: g_if end\n"
      "  case (N)\n"
      "    1: begin: g_case end\n"
      "    default: begin: g_default end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kGenerateFor));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kGenerateIf));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kGenerateCase));
}

// §3.3 lists "Specify blocks" as a module construct. The dispatcher
// routes `specify` to ParseSpecifyBlock, emitting kSpecifyBlock. Observe
// the parser accepting an empty specify block at module-item scope.
TEST(ModuleItems, SpecifyBlocks) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kSpecifyBlock));
}

// §3.3 closes with a simple example presented as "a module that
// represents a 2-to-1 multiplexer", combining the enclosure rule, an
// ANSI port list, and a procedural block. Replicate the example
// verbatim and observe the parser producing a single ModuleDecl named
// `mux2to1` whose body holds the always_comb block, anchoring the
// example to the parser-stage code that satisfies §3.3.
TEST(ModuleEnclosure, Mux2to1ExampleParses) {
  auto r = Parse(
      "module mux2to1 (input wire a, b, sel,\n"
      "                output logic y);\n"
      "  always_comb begin\n"
      "    if (sel) y = a;\n"
      "    else     y = b;\n"
      "  end\n"
      "endmodule: mux2to1\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "mux2to1");
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 4u);
  EXPECT_TRUE(HasAlwaysOfKind(r.cu->modules[0]->items,
                              AlwaysKind::kAlwaysComb));
}

// §3.3's NOTE states the preceding list is not all-inclusive: the
// dispatcher must accept module-item constructs beyond the enumerated
// set without rejecting them. A clocking block (Clause 14) is one such
// non-listed item that ParseModuleItem still admits via
// TryParseClockingOrVerification. Observe a module body carrying both a
// listed item (continuous assignment) and a non-listed item (clocking
// block) parsing cleanly.
TEST(ModuleEnclosure, ListIsNotAllInclusive) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, d;\n"
      "  assign d = 1'b0;\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kContAssign));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kClockingBlock));
}

}  // namespace
