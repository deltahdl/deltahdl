// §3.4: The program building block is enclosed between the keywords
// program ... endprogram. A program block can contain data declarations,
// class definitions, subroutine definitions, object instances, and one or
// more initial or final procedures. It cannot contain always procedures,
// primitive instances, module instances, interface instances, or other
// program instances.

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- Enclosure between program / endprogram ---

TEST(ProgramBlockParsing, ProgramEndprogramEnclosureProducesProgramDecl) {
  auto r = Parse("program p; endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "p");
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

TEST(ProgramBlockParsing, ProgramBodyTerminatesOnlyAtEndprogram) {
  // Without the endprogram keyword the parser cannot close the program block.
  auto r = Parse("program p; initial begin end\n");
  EXPECT_TRUE(r.has_errors);
}

// --- Permitted contents ---

TEST(ProgramBlockParsing, ProgramAcceptsDataDeclaration) {
  auto r = Parse("program p; logic [7:0] data; endprogram\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_GE(r.cu->programs[0]->items.size(), 1u);
}

TEST(ProgramBlockParsing, ProgramAcceptsClassDefinition) {
  auto r = Parse(
      "program p;\n"
      "  class C; int x; endclass\n"
      "endprogram\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ProgramBlockParsing, ProgramAcceptsSubroutineDefinitions) {
  auto r = Parse(
      "program p;\n"
      "  function int f(); return 0; endfunction\n"
      "  task t(); endtask\n"
      "endprogram\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ProgramBlockParsing, ProgramAcceptsObjectInstance) {
  auto r = Parse(
      "class C; int x; endclass\n"
      "program p;\n"
      "  C obj;\n"
      "  initial obj = new();\n"
      "endprogram\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ProgramBlockParsing, ProgramAcceptsInitialProcedure) {
  auto r = Parse("program p; initial begin end endprogram\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ProgramBlockParsing, ProgramAcceptsFinalProcedure) {
  auto r = Parse("program p; final begin end endprogram\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ProgramBlockParsing, ProgramAcceptsMultipleInitialAndFinalProcedures) {
  auto r = Parse(
      "program p;\n"
      "  initial begin end\n"
      "  initial begin end\n"
      "  final begin end\n"
      "endprogram\n");
  EXPECT_FALSE(r.has_errors);
}

// --- Prohibited contents (§3.4) ---

TEST(ProgramBlockParsing, ProgramRejectsAlwaysProcedure) {
  auto r = Parse("program p; always @(*) begin end endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ProgramBlockParsing, ProgramRejectsGatePrimitiveInstance) {
  auto r = Parse(
      "program p;\n"
      "  wire a, b, c;\n"
      "  and g1(c, a, b);\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ProgramBlockParsing, ProgramRejectsUserDefinedPrimitiveInstance) {
  auto r = Parse(
      "primitive my_udp(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "program p;\n"
      "  wire x, z;\n"
      "  my_udp u1(x, z);\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ProgramBlockParsing, ProgramRejectsModuleInstance) {
  auto r = Parse(
      "module sub; endmodule\n"
      "program p;\n"
      "  sub inst();\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ProgramBlockParsing, ProgramRejectsInterfaceInstance) {
  auto r = Parse(
      "interface bus; endinterface\n"
      "program p;\n"
      "  bus inst();\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ProgramBlockParsing, ProgramRejectsNestedProgramDeclaration) {
  auto r = Parse(
      "program outer;\n"
      "  program inner; endprogram\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ProgramBlockParsing, ProgramRejectsOtherProgramInstance) {
  auto r = Parse(
      "program other; endprogram\n"
      "program p;\n"
      "  other inst();\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
