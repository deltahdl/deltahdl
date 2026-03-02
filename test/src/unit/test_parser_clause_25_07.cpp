// §25.7: Tasks and functions in interfaces

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA29, ImportMultipleIdentifiers) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read, Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_EQ(mp->ports[0].name, "Read");
  EXPECT_TRUE(mp->ports[1].is_import);
  EXPECT_EQ(mp->ports[1].name, "Write");
}

// modport_tf_ports_declaration ::=
//   import_export modport_tf_port { , modport_tf_port }
TEST(ParserA29, ImportSingleIdentifier) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_EQ(mp->ports[0].name, "Read");
}

// Mixed modport_ports_declarations
TEST(ParserA29, MixedDirImportExport) {
  auto r = Parse(
      "interface bus;\n"
      "  logic req, gnt;\n"
      "  modport target(\n"
      "    input req,\n"
      "    output gnt,\n"
      "    import Read,\n"
      "    export Write\n"
      "  );\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 4u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].direction, Direction::kOutput);
  EXPECT_TRUE(mp->ports[2].is_import);
  EXPECT_TRUE(mp->ports[3].is_export);
}

TEST(ParserA29, AttrOnImportPort) {
  EXPECT_TRUE(
      ParseOk("interface bus;\n"
              "  modport target((* synthesis *) import Read);\n"
              "endinterface\n"));
}

// --- Modport import/export (LRM §25.5, §25.7) ---
TEST(ParserSection25, ModportImportExportName) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read, export Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  EXPECT_EQ(mp->name, "target");
  ASSERT_EQ(mp->ports.size(), 2);
}

TEST(ParserSection25, ModportImportExportPorts) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read, export Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2);
  VerifyImportExportPort(mp->ports[0], true, false, "Read");
  VerifyImportExportPort(mp->ports[1], false, true, "Write");
}

TEST(ParserSection25, ModportImportWithDirectionSecond) {
  auto r = Parse(
      "interface bus;\n"
      "  logic data;\n"
      "  modport target(input data, import Read);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2);
  EXPECT_FALSE(mp->ports[0].is_export);
  EXPECT_TRUE(mp->ports[1].is_import);
  EXPECT_EQ(mp->ports[1].name, "Read");
}

// interface_or_generate_item ::= { attribute_instance } extern_tf_declaration
// extern_tf_declaration ::= extern method_prototype ;
// Verify extern function prototype inside an interface.
TEST(SourceText, ExternFunctionPrototypeInInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern function void compute(input int x);\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  ASSERT_GE(ifc->items.size(), 1u);
  EXPECT_EQ(ifc->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(ifc->items[0]->name, "compute");
  EXPECT_TRUE(ifc->items[0]->is_extern);
  // Prototype only — no body statements.
  EXPECT_TRUE(ifc->items[0]->func_body_stmts.empty());
}

// extern_tf_declaration ::= extern method_prototype ;
// method_prototype ::= task_prototype — extern task prototype.
TEST(SourceText, ExternTaskPrototypeInInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern task run();\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  ASSERT_GE(ifc->items.size(), 1u);
  EXPECT_EQ(ifc->items[0]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(ifc->items[0]->name, "run");
  EXPECT_TRUE(ifc->items[0]->is_extern);
  EXPECT_TRUE(ifc->items[0]->func_body_stmts.empty());
}

TEST(ParserA27, TaskBodyInterfaceScope) {
  auto r = Parse(
      "interface intf;\n"
      "  extern task my_task();\n"
      "endinterface\n"
      "task intf.my_task();\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA29, ImportFunctionPrototype) {
  auto r = Parse(
      "interface bus;\n"
      "  modport init(import function int compute(input int a));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_EQ(mp->ports[0].prototype->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(mp->ports[0].prototype->name, "compute");
}

TEST(ParserA29, ImportTaskNoArgs) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import task doWork);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_EQ(mp->ports[0].prototype->name, "doWork");
}

TEST(ParserA29, ImportFunctionVoidReturn) {
  EXPECT_TRUE(
      ParseOk("interface bus;\n"
              "  modport init(import function void reset());\n"
              "endinterface\n"));
}

// Verify import/export flags are mutually exclusive in AST
TEST(ParserA29, ImportFlag_NotExport) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_FALSE(mp->ports[0].is_export);
}

}  // namespace
