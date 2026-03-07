#include "fixture_elaborator.h"
#include "fixture_parser.h"

using namespace delta;
namespace {

// §6.15: A class variable holds a handle to a class object.
TEST(ParserSection6, ClassVariableDecl) {
  auto r = Parse(
      "class Packet;\n"
      "  int payload;\n"
      "endclass\n"
      "module m;\n"
      "  Packet pkt;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ModuleItem* var_item = nullptr;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kVarDecl && it->name == "pkt") {
      var_item = it;
      break;
    }
  }
  ASSERT_NE(var_item, nullptr);
  EXPECT_EQ(var_item->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(var_item->data_type.type_name, "Packet");
}

// §6.15: Class variable initialized to null by default.
TEST(ParserSection6, ClassVariableNullCheck) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  C obj;\n"
              "  int r;\n"
              "  initial r = (obj == null) ? 1 : 0;\n"
              "endmodule\n"));
}

// §6.15: Class variable can be assigned via new.
TEST(ParserSection6, ClassVariableNew) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  C obj;\n"
              "  initial obj = new;\n"
              "endmodule\n"));
}

// §6.15: Class handle assignment between variables.
TEST(ParserSection6, ClassHandleAssignment) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  C a, b;\n"
              "  initial begin\n"
              "    a = new;\n"
              "    b = a;\n"
              "  end\n"
              "endmodule\n"));
}

// §6.15: Class variable elaborates ok.
TEST(Elaboration, ClassVariableElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Pkt;\n"
      "  int data;\n"
      "endclass\n"
      "module top;\n"
      "  Pkt p;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
