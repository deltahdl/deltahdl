#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// Return the body items of the first program declaration in the parse result.
// Program bodies are parsed through the shared module-item parse path
// (Parser::ParseProgramDecl -> ParseModuleItem), so the A.1.7 program-item
// grammar is observed by checking the kinds recorded for each accepted
// construct, mirroring the approach used for interface items (A.1.6).
const std::vector<ModuleItem*>& ProgItems(ParseResult& r) {
  static const std::vector<ModuleItem*> kEmpty;
  if (!r.cu || r.cu->programs.empty()) return kEmpty;
  return r.cu->programs[0]->items;
}

// --- program_item ::= port_declaration ; | non_port_program_item ---
// The first alternative is a non-ANSI port declaration appearing in the program
// body. The body parse path applies the port-declaration grammar and back-fills
// the direction of the matching entry in the program's port list.
TEST(ProgramItem, NonAnsiPortDeclaration) {
  auto r = Parse(
      "program p(a);\n"
      "  input a;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  ASSERT_EQ(r.cu->programs[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->programs[0]->ports[0].direction, Direction::kInput);
}

// program_item's first alternative requires a trailing semicolon after the
// port_declaration (it is the literal ';' in `program_item ::= port_declaration
// ;`). A body port declaration that omits it is rejected.
TEST(ProgramItem, NonAnsiPortDeclarationMissingSemicolonIsError) {
  auto r = Parse(
      "program p(a);\n"
      "  input a\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  // A program body reads its non-ANSI port declarations through
  // Parser::ParseNonAnsiPortDecls, which files the missing ';' under §23.2.2.1
  // with the module form it shares. `endprogram` stands where the ';' belongs,
  // on line 3.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endprogram'", 3, "23.2.2.1"));
}

// program_item ::= port_declaration ; | non_port_program_item — both top-level
// alternatives may appear within a single program body; the parse path
// dispatches each in turn (the port declaration back-fills the port direction
// while the non-port items are recorded as body items).
TEST(ProgramItem, PortDeclarationAndNonPortItemsCoexist) {
  auto r = Parse(
      "program p(a);\n"
      "  input a;\n"
      "  wire w;\n"
      "  assign w = a;\n"
      "  initial x = 0;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  ASSERT_EQ(r.cu->programs[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->ports[0].direction, Direction::kInput);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kContAssign));
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kInitialBlock));
}

// --- non_port_program_item ---
// non_port_program_item ::=
//     { attribute_instance } continuous_assign
//   | { attribute_instance } module_or_generate_item_declaration
//   | { attribute_instance } initial_construct
//   | { attribute_instance } final_construct
//   | { attribute_instance } concurrent_assertion_item
//   | timeunits_declaration
//   | program_generate_item

TEST(NonPortProgramItem, ContinuousAssign) {
  auto r = Parse(
      "program p;\n"
      "  wire w;\n"
      "  assign w = a;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kContAssign));
}

// module_or_generate_item_declaration covers the declaration constructs shared
// with modules (parameters, genvars, clocking, etc.); a parameter declaration
// is a representative of that alternative.
TEST(NonPortProgramItem, ModuleOrGenerateItemDeclaration) {
  auto r = Parse(
      "program p;\n"
      "  localparam int W = 2;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kParamDecl));
}

TEST(NonPortProgramItem, InitialConstruct) {
  auto r = Parse(
      "program p;\n"
      "  initial x = 0;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kInitialBlock));
}

TEST(NonPortProgramItem, FinalConstruct) {
  auto r = Parse(
      "program p;\n"
      "  final x = 1;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kFinalBlock));
}

// concurrent_assertion_item is admitted as a program item; it is recorded as an
// assert-property item.
TEST(NonPortProgramItem, ConcurrentAssertionItem) {
  auto r = Parse(
      "program p;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kAssertProperty));
}

// timeunits_declaration is the only non_port_program_item alternative without a
// leading attribute_instance; the body parse path records it on the program
// declaration rather than as an item.
TEST(NonPortProgramItem, TimeunitsDeclaration) {
  auto r = Parse(
      "program p;\n"
      "  timeunit 1ns;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(r.cu->programs[0]->has_timeunit);
}

// The first five alternatives permit a leading run of attribute_instances; the
// shared parse path collects them and attaches them to the resulting item.
TEST(NonPortProgramItem, AttributeInstancePrefix) {
  auto r = Parse(
      "program p;\n"
      "  (* keep *) assign w = a;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(ProgItems(r), ModuleItemKind::kContAssign);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->attrs.size(), 1u);
  EXPECT_EQ(item->attrs[0].name, "keep");
}

// --- program_generate_item ---
// program_generate_item ::=
//     loop_generate_construct
//   | conditional_generate_construct
//   | generate_region
//   | elaboration_severity_system_task

TEST(ProgramGenerateItem, LoopGenerateConstruct) {
  auto r = Parse(
      "program p;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin\n"
      "    initial x = i;\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kGenerateFor));
}

TEST(ProgramGenerateItem, ConditionalGenerateConstructIf) {
  auto r = Parse(
      "program p;\n"
      "  if (1) initial x = 0;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kGenerateIf));
}

TEST(ProgramGenerateItem, ConditionalGenerateConstructCase) {
  auto r = Parse(
      "program p;\n"
      "  case (1)\n"
      "    0: initial x = 0;\n"
      "    default: initial y = 0;\n"
      "  endcase\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kGenerateCase));
}

// A generate_region flattens its contained generate items into the enclosing
// item list; observing the inner item confirms the generate/endgenerate region
// was parsed as a program item.
TEST(ProgramGenerateItem, GenerateRegion) {
  auto r = Parse(
      "program p;\n"
      "  generate\n"
      "    initial x = 0;\n"
      "  endgenerate\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kInitialBlock));
}

TEST(ProgramGenerateItem, ElaborationSeveritySystemTask) {
  auto r = Parse(
      "program p;\n"
      "  $error(\"bad\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kElabSystemTask));
}

// --- non_port_program_item admits no specify_block or specparam_declaration
// ---
// A.1.4's non_port_module_item lists specify_block and
// { attribute_instance } specparam_declaration; non_port_program_item lists
// neither, and §30.3 has the specify block "defined within a module" while
// §6.20.5 has a specparam "declared inside a module or specify block". Each
// was accepted in a program body silently and recorded as an item of it.

TEST(NonPortProgramItem, ErrorSpecifyBlockInProgramIsRejected) {
  auto r = Parse(
      "program p;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "  initial x = 0;\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "specify block must appear inside a module declaration", 2,
      "30.3"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(NonPortProgramItem, ErrorSpecparamInProgramIsRejected) {
  auto r = Parse(
      "program p;\n"
      "  specparam tRise = 150;\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "specparam declaration must appear inside a module or a specify block", 2,
      "6.20.5"));
}

// --- non_port_program_item admits no net_alias, bind_directive or
// parameter_override ---
// A.1.4's module_common_item lists net_alias and bind_directive and its
// module_or_generate_item lists parameter_override; non_port_program_item lists
// none of the three. Each was accepted in a program body silently and recorded
// as an item of it; each is now reported under A.1.7 at its keyword and still
// read, so that the body resumes after it.

TEST(NonPortProgramItem, ErrorNetAliasInProgramIsRejected) {
  auto r = Parse(
      "program p;\n"
      "  alias a = b;\n"
      "  initial x = 0;\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(r.diags, "a net alias is not an item of a program",
                            2, "A.1.7"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(NonPortProgramItem, ErrorBindDirectiveInProgramIsRejected) {
  auto r = Parse(
      "program p;\n"
      "  bind m chk c();\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a bind directive is not an item of a program", 2, "A.1.7"));
}

TEST(NonPortProgramItem, ErrorDefparamInProgramIsRejected) {
  auto r = Parse(
      "program p;\n"
      "  defparam u.w = 1;\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a defparam statement is not an item of a program", 2, "A.1.7"));
}

// --- non_port_program_item admits a concurrent_assertion_item and not
// A.1.4's assertion_item ---
// assertion_item's other alternative is A.6.10's
// deferred_immediate_assertion_item, and §16.4.3 has a deferred assertion
// outside procedural code "treated as if it were contained in an always_comb
// procedure", which §24.3 has a program not contain. Both deferral forms were
// accepted in a program body silently.
TEST(NonPortProgramItem, ErrorDeferredImmediateAssertionInProgramIsRejected) {
  auto r = Parse(
      "program p;\n"
      "  a1: assert #0 (x);\n"
      "  cover final (y);\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a deferred immediate assertion is not an item of a program", 2,
      "A.1.7"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a deferred immediate assertion is not an item of a program", 3,
      "A.1.7"));
}

// A concurrent_assertion_item reaches A.4.1.4's checker_instantiation, and
// §17.3 has a checker instantiated "wherever a concurrent assertion may
// appear"; the parser reported every instantiation in a program under §24.3,
// the checker's with the module's it forbids.
TEST(NonPortProgramItem, ConcurrentAssertionItemCheckerInstantiation) {
  auto r = Parse(
      "checker chk(input logic a);\n"
      "endchecker\n"
      "program p;\n"
      "  chk c(x);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kModuleInst));
}

// A.4.1.4 names the checker by a ps_checker_identifier, `[ package_scope ]
// checker_identifier`, where the module, interface and program instantiations
// §24.3 forbids name their cell by an identifier alone.
TEST(NonPortProgramItem, PackageScopedCheckerInstantiation) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  checker chk(input logic a);\n"
              "  endchecker\n"
              "endpackage\n"
              "program p;\n"
              "  pkg::chk c(x);\n"
              "endprogram\n"));
}

// §24.3's report on an instantiation is made for a cell the parse has seen
// declared as a module, an interface or a program; a cell declared after the
// program, or in another file, is the elaborator's to report.
TEST(NonPortProgramItem, InstantiationOfCellDeclaredLaterIsLeftToElaboration) {
  auto r = Parse(
      "program p;\n"
      "  sub u0();\n"
      "endprogram\n"
      "module sub; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Footnote 5 to program_generate_item: "it shall be illegal for a
// program_generate_item to include any item that would be illegal in a
// program_declaration outside a program_generate_item".
TEST(ProgramGenerateItem, AdmitsProgramItemsOnly) {
  auto r = Parse(
      "program p;\n"
      "  if (1) begin : g\n"
      "    defparam u.w = 1;\n"
      "  end\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a defparam statement is not an item of a program", 3, "A.1.7"));
}

}  // namespace
