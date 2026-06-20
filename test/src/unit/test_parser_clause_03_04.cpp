

#include <algorithm>
#include <string_view>
#include <vector>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ProgramBlockParsing, ProgramEndprogramEnclosureProducesProgramDecl) {
  auto r = Parse("program p; endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "p");
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

TEST(ProgramBlockParsing, ProgramBodyTerminatesOnlyAtEndprogram) {
  auto r = Parse("program p; initial begin end\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ProgramBlockParsing, ProgramScopeEncapsulatesItems) {
  auto r = Parse(
      "program p1;\n"
      "  int data;\n"
      "  task t(); endtask\n"
      "  function int f(); return 0; endfunction\n"
      "endprogram\n"
      "program p2;\n"
      "  int data;\n"
      "  task t(); endtask\n"
      "  function int f(); return 0; endfunction\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 2u);

  const auto& p1 = *r.cu->programs[0];
  const auto& p2 = *r.cu->programs[1];
  EXPECT_EQ(p1.name, "p1");
  EXPECT_EQ(p2.name, "p2");
  EXPECT_GE(p1.items.size(), 3u);
  EXPECT_GE(p2.items.size(), 3u);
  auto names_in = [](const ModuleDecl& m) {
    std::vector<std::string_view> ns;
    for (const auto* it : m.items) ns.push_back(it->name);
    return ns;
  };
  auto p1_names = names_in(p1);
  auto p2_names = names_in(p2);
  EXPECT_NE(std::find(p1_names.begin(), p1_names.end(), "data"),
            p1_names.end());
  EXPECT_NE(std::find(p1_names.begin(), p1_names.end(), "t"), p1_names.end());
  EXPECT_NE(std::find(p1_names.begin(), p1_names.end(), "f"), p1_names.end());
  EXPECT_NE(std::find(p2_names.begin(), p2_names.end(), "data"),
            p2_names.end());
  EXPECT_NE(std::find(p2_names.begin(), p2_names.end(), "t"), p2_names.end());
  EXPECT_NE(std::find(p2_names.begin(), p2_names.end(), "f"), p2_names.end());
}

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

TEST(ProgramBlockParsing, ProgramAcceptsPortListWithDirections) {
  auto r = Parse(
      "program test (input clk, input [16:1] addr, inout [7:0] data);\n"
      "  initial begin end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  const auto& prog = *r.cu->programs[0];
  EXPECT_EQ(prog.name, "test");
  EXPECT_EQ(prog.decl_kind, ModuleDeclKind::kProgram);
  ASSERT_EQ(prog.ports.size(), 3u);
  EXPECT_EQ(prog.ports[0].name, "clk");
  EXPECT_EQ(prog.ports[0].direction, Direction::kInput);
  EXPECT_EQ(prog.ports[1].name, "addr");
  EXPECT_EQ(prog.ports[1].direction, Direction::kInput);
  EXPECT_EQ(prog.ports[2].name, "data");
  EXPECT_EQ(prog.ports[2].direction, Direction::kInout);
}

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
