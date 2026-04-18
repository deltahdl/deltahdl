// §25.7

#include "fixture_elaborator.h"

namespace {

TEST(InterfaceSubroutines, InterfaceWithSubroutinesElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc;\n"
      "  function automatic int xform(int v); return v; endfunction\n"
      "  task send; endtask\n"
      "endinterface\n",
      f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ModportDeclarationElaboration, ImportExportModportElaborates) {
  EXPECT_TRUE(
      ElabOk("interface ifc;\n"
             "  modport mp(import Read, export Write);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ModportDeclarationElaboration, ImportPrototypeElaborates) {
  EXPECT_TRUE(
      ElabOk("interface ifc;\n"
             "  modport mp(\n"
             "    import function int compute(int a),\n"
             "    import task do_work(int x)\n"
             "  );\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceSubroutines, MultipleInterfacesWithSubroutinesElaborate) {
  EXPECT_TRUE(
      ElabOk("interface a_if;\n"
             "  function automatic int fa(int v); return v + 1; endfunction\n"
             "endinterface\n"
             "interface b_if;\n"
             "  task tb; endtask\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceSubroutines, ExternPrototypeWithoutBodyElaborates) {
  EXPECT_TRUE(
      ElabOk("interface ifc;\n"
             "  extern function int compute(input int a);\n"
             "  extern task run(input int x);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceSubroutines, ExternForkjoinTaskPrototypeElaborates) {
  EXPECT_TRUE(
      ElabOk("interface ifc;\n"
             "  extern forkjoin task parallel_run(input int id);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceSubroutines, HierarchicalTaskBodyElaborates) {
  EXPECT_TRUE(
      ElabOk("interface ifc;\n"
             "  extern task my_task(input int x);\n"
             "endinterface\n"
             "task ifc.my_task(input int x);\n"
             "endtask\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceSubroutines, HierarchicalFunctionBodyElaborates) {
  EXPECT_TRUE(
      ElabOk("interface ifc;\n"
             "  extern function int my_func(input int a);\n"
             "endinterface\n"
             "function int ifc.my_func(input int a);\n"
             "  return a;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ModportDeclarationElaboration, ImportPrototypeWithDefaultArgElaborates) {
  EXPECT_TRUE(
      ElabOk("interface ifc;\n"
             "  modport mp(import function int compute(int a = 0));\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
