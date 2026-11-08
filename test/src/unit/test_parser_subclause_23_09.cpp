#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_class.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(ModuleScopeParse, TypeParameterNameIsNotATypeInALaterModule) {
  auto r = Parse(
      "module a #(parameter type TP = logic) (); endmodule\n"
      "module b #(parameter TP = 1) (); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  auto* mod_b = r.cu->modules[1];
  EXPECT_EQ(mod_b->name, "b");
  ASSERT_EQ(mod_b->params.size(), 1u);
  EXPECT_EQ(mod_b->params[0].first, "TP");
  EXPECT_TRUE(mod_b->type_param_names.empty());
}

TEST(ModuleScopeParse, ModuleTypedefNameIsNotATypeInALaterModule) {
  auto r = Parse(
      "module a; typedef int T; endmodule\n"
      "module b #(parameter T = 1) (); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  auto* mod_b = r.cu->modules[1];
  EXPECT_EQ(mod_b->name, "b");
  ASSERT_EQ(mod_b->params.size(), 1u);
  EXPECT_EQ(mod_b->params[0].first, "T");
  EXPECT_TRUE(mod_b->type_param_names.empty());
}

TEST(ModuleScopeParse, TypeParameterIsStillATypeInsideItsOwnModule) {
  auto r = Parse(
      "module a #(parameter type TP = logic) ();\n"
      "  TP x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* item = FindItemByName(r.cu->modules[0]->items, "x");
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(item->data_type.type_name, "TP");
}

TEST(ModuleScopeParse, CompilationUnitTypedefIsATypeInEveryModule) {
  auto r = Parse(
      "typedef int T;\n"
      "module a;\n"
      "  T x;\n"
      "endmodule\n"
      "module b;\n"
      "  T x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  for (auto* mod : r.cu->modules) {
    auto* item = FindItemByName(mod->items, "x");
    ASSERT_NE(item, nullptr) << "no declaration of x in module " << mod->name;
    EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
    EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed);
    EXPECT_EQ(item->data_type.type_name, "T");
  }
}

TEST(ModuleScopeParse, TaskTypedefNameIsNotATypeAfterItsTask) {
  auto r = Parse(
      "module m;\n"
      "  task t; typedef int T; endtask\n"
      "  localparam T = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* item = FindItemByName(r.cu->modules[0]->items, "T");
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kImplicit);
}

TEST(ModuleScopeParse, FunctionTypedefNameIsNotATypeAfterItsFunction) {
  auto r = Parse(
      "module m;\n"
      "  function int f; typedef int T; f = 0; endfunction\n"
      "  localparam T = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* item = FindItemByName(r.cu->modules[0]->items, "T");
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kImplicit);
}

TEST(ModuleScopeParse, BlockTypedefNameIsNotATypeAfterItsBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin typedef int T; end\n"
      "  localparam T = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* item = FindItemByName(r.cu->modules[0]->items, "T");
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kImplicit);
}

TEST(ModuleScopeParse, ForkTypedefNameIsNotATypeAfterItsFork) {
  auto r = Parse(
      "module m;\n"
      "  initial fork typedef int T; join\n"
      "  localparam T = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* item = FindItemByName(r.cu->modules[0]->items, "T");
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kImplicit);
}

TEST(ModuleScopeParse, GenerateBlockTypedefNameIsNotATypeAfterIt) {
  auto r = Parse(
      "module m;\n"
      "  generate if (1) begin typedef int T; end endgenerate\n"
      "  localparam T = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* item = FindItemByName(r.cu->modules[0]->items, "T");
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kImplicit);
}

TEST(ModuleScopeParse, TaskTypedefIsStillATypeInsideItsOwnTask) {
  auto r = Parse(
      "module m;\n"
      "  task t;\n"
      "    typedef int T;\n"
      "    T x;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* task = FindItemByName(r.cu->modules[0]->items, "t");
  ASSERT_NE(task, nullptr);
  const Stmt* decl = nullptr;
  for (const auto* s : task->func_body_stmts) {
    if (s->kind == StmtKind::kVarDecl && s->var_name == "x") decl = s;
  }
  ASSERT_NE(decl, nullptr);
  EXPECT_EQ(decl->var_decl_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(decl->var_decl_type.type_name, "T");
}

TEST(ModuleScopeParse, PackageTypedefNameIsNotATypeInALaterModule) {
  auto r = Parse(
      "package p;\n"
      "  typedef int T;\n"
      "endpackage\n"
      "module m #(parameter T = 1) (); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "T");
  EXPECT_TRUE(r.cu->modules[0]->type_param_names.empty());
}

TEST(ModuleScopeParse, PackageTypedefIsATypeInAModuleThatImportsIt) {
  auto r = Parse(
      "package p;\n"
      "  typedef int T;\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "  T x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* item = FindItemByName(r.cu->modules[0]->items, "x");
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(item->data_type.type_name, "T");
}

TEST(ModuleScopeParse, PackageImportDoesNotReachAModuleThatDidNotImport) {
  auto r = Parse(
      "package p;\n"
      "  typedef int T;\n"
      "endpackage\n"
      "module a;\n"
      "  import p::*;\n"
      "  T x;\n"
      "endmodule\n"
      "module b;\n"
      "  localparam T = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  auto* x = FindItemByName(r.cu->modules[0]->items, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->data_type.kind, DataTypeKind::kNamed);
  auto* t = FindItemByName(r.cu->modules[1]->items, "T");
  ASSERT_NE(t, nullptr);
  EXPECT_EQ(t->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(t->data_type.kind, DataTypeKind::kImplicit);
}

TEST(ModuleScopeParse, ExplicitPackageImportTakesOnlyTheNameItWrites) {
  auto r = Parse(
      "package p;\n"
      "  typedef int T;\n"
      "  typedef int U;\n"
      "endpackage\n"
      "module m;\n"
      "  import p::T;\n"
      "  T x;\n"
      "  localparam U = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* x = FindItemByName(r.cu->modules[0]->items, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(x->data_type.type_name, "T");
  auto* u = FindItemByName(r.cu->modules[0]->items, "U");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(u->data_type.kind, DataTypeKind::kImplicit);
}

TEST(ModuleScopeParse, PackageImportInAModuleHeaderIsATypeInThePortList) {
  auto r = Parse(
      "package p;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "module m import p::*; (input byte_t a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[0].data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(r.cu->modules[0]->ports[0].data_type.type_name, "byte_t");
}

TEST(ModuleScopeParse, PackageNettypeIsANettypeInAModuleThatImportsIt) {
  auto r = Parse(
      "package p;\n"
      "  nettype logic [7:0] nt;\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "  nt #5 w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* w = FindItemByName(r.cu->modules[0]->items, "w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(w->data_type.type_name, "nt");
}

TEST(ModuleScopeParse, ClassTypedefNameIsNotATypeInALaterModule) {
  auto r = Parse(
      "class C;\n"
      "  typedef int T;\n"
      "endclass\n"
      "module m #(parameter T = 1) (); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "T");
  EXPECT_TRUE(r.cu->modules[0]->type_param_names.empty());
}

TEST(ModuleScopeParse, BaseClassTypedefIsATypeInADerivedClass) {
  auto r = Parse(
      "class C;\n"
      "  typedef int T;\n"
      "endclass\n"
      "class D extends C;\n"
      "  T x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  const ClassMember* x = nullptr;
  for (const auto* member : r.cu->classes[1]->members) {
    if (member->name == "x") x = member;
  }
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(x->data_type.type_name, "T");
}

TEST(ModuleScopeParse, ClassNameIsStillATypeAfterItsOwnDeclaration) {
  auto r = Parse(
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  C h;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* h = FindItemByName(r.cu->modules[0]->items, "h");
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(h->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(h->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(h->data_type.type_name, "C");
}

}  // namespace
